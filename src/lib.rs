// Author Axel Viala <axel.viala@darnuria.eu>
// Done on free time inspired a lot by pymysqlreplication own implementation.
// Licence MIT + APACHE 2.

mod gtid_set;

pub use gtid_set::GtidSet;

use std::cmp::Ordering;
use std::io::Write;
use std::{
    error::Error,
    fmt::{Debug, Display},
    io,
};

/// A MySql GTID: Global Transaction IDentifier.
///
/// https://dev.mysql.com/doc/refman/5.7/en/replication-gtids-concepts.html
#[derive(PartialEq, Eq, Clone)]
pub struct Gtid {
    /// The UUID in binary forms caches line welcomes you.
    sid: [u8; 16],
    /// The intervals shall be sorted.
    intervals: Vec<(u64, u64)>,
}

impl Gtid {
    /// Construct a Gtid from a SID and a GNO, you mostly want to use it with `GtidEvent` type of
    /// [Mysql-common](https://github.com/blackbeam/rust_mysql_common/blob/master/src/binlog/events/gtid_event.rs) crate.
    ///
    /// Note that a gno MUST BE non zero.
    pub fn from_sid_gno(sid: [u8; 16], gno: u64) -> Gtid {
        debug_assert!(gno != 0);
        Gtid {
            sid,
            intervals: vec![(gno, gno + 1)],
        }
    }

    /// SID as binary representation
    pub fn sid(&self) -> [u8; 16] {
        self.sid
    }

    /// SID as textual byte array
    pub fn sid_as_bytes(&self) -> [u8; 36] {
        uuid_bin_to_hex(self.sid)
    }

    /// SID as textual UUID.
    pub fn sid_as_string(&self) -> String {
        let sid: [u8; 36] = uuid_bin_to_hex(self.sid);
        String::from_utf8_lossy(&sid[..]).to_string()
    }

    /// Unstable may be removed.
    pub fn raw_gtid_unchecked(sid: [u8; 36]) -> Result<Gtid, GtidError> {
        let sid = parse_uuid(&sid)?;

        Ok(Gtid {
            sid,
            intervals: vec![],
        })
    }

    /// Create a Gtid with intervals.
    ///
    /// Intervals will be checked.
    pub fn with_intervals(sid: [u8; 36], intervals: Vec<(u64, u64)>) -> Result<Gtid, GtidError> {
        let sid = parse_uuid(&sid)?;

        let mut gtid = Gtid {
            sid,
            intervals: Vec::with_capacity(intervals.len()),
        };
        for interval in intervals {
            gtid.add_interval(&interval)?;
        }
        Ok(gtid)
    }

    /// Add an interval but does not check assume interval is correctly formed
    fn add_interval_unchecked(&mut self, interval: &(u64, u64)) {
        let mut interval = *interval;

        // TODO: Do it in place with a filter.
        let mut new: Vec<(u64, u64)> = Vec::with_capacity(self.intervals.len());
        for current in self.intervals.iter() {
            if interval.0 == current.1 {
                interval = (current.0, interval.1);
                continue;
            }

            if interval.1 == current.0 {
                interval = (interval.0, current.1);
                continue;
            }
            new.push(*current);
        }

        new.push(interval);
        new.sort();
        self.intervals = new;
    }

    /// Add a raw interval into the gtid.
    fn add_interval(&mut self, interval: &(u64, u64)) -> Result<(), GtidError> {
        if interval.0 == 0 || interval.1 == 0 {
            return Err(GtidError::ZeroInInterval);
        }

        if interval.0 > interval.1 {
            return Err(GtidError::IntervalBadlyOrdered);
        }

        if self.intervals.iter().any(|x| overlap(x, interval)) {
            return Err(GtidError::OverlappingInterval);
        }

        self.add_interval_unchecked(interval);
        Ok(())
    }

    fn sub_interval_unchecked(&mut self, interval: &(u64, u64)) {
        // TODO: Do it in place with a filter.
        let mut new: Vec<(u64, u64)> = Vec::with_capacity(self.intervals.len());
        for current in self.intervals.iter() {
            if overlap(current, interval) {
                if current.0 < interval.0 {
                    new.push((current.0, interval.0));
                }
                if current.1 > interval.1 {
                    new.push((interval.1, current.1))
                }
            } else {
                new.push(*current)
            }
        }

        new.sort();
        self.intervals = new;
    }

    /// Remove an interval from intervals.
    ///
    /// Does not check for Zero in interval, interval badly ordered or overlap.
    /// Assume interval is well formed.
    pub fn sub_interval(&mut self, interval: &(u64, u64)) -> Result<(), GtidError> {
        if interval.0 == 0 || interval.1 == 0 {
            return Err(GtidError::ZeroInInterval);
        }

        if interval.0 > interval.1 {
            return Err(GtidError::IntervalBadlyOrdered);
        }

        // Nothing to do in this case.
        if !self.intervals.iter().any(|x| overlap(x, interval)) {
            return Ok(());
        }

        self.sub_interval_unchecked(interval);
        Ok(())
    }

    pub fn contains(&self, other: &Gtid) -> bool {
        if self.sid != other.sid {
            return false;
        }

        other
            .intervals
            .iter()
            .all(|them| self.intervals.iter().any(|me| contains(me, them)))
    }

    /// Merge intervals from an other Gtid.
    pub fn include_transactions(&mut self, other: &Gtid) -> Result<(), GtidError> {
        if self.sid != other.sid {
            return Err(GtidError::SidNotMatching);
        }

        for interval in other.intervals.iter() {
            // We don't need to check for correctness
            // of interval Gtid is supposed wellformed.
            self.add_interval_unchecked(interval);
        }

        Ok(())
    }

    /// Remove intervals from an other Gtid.
    pub fn remove_transactions(&mut self, other: &Gtid) -> Result<(), GtidError> {
        if self.sid != other.sid {
            return Err(GtidError::SidNotMatching);
        }

        for interval in other.intervals.iter() {
            // We assume intervals are OK.
            self.sub_interval_unchecked(interval);
        }

        Ok(())
    }

    /// Parse from binary a [Gtid]
    ///
    /// For binary format description see [Gtid::serialize]
    ///
    /// Known issue: sid need to be validated and not accepted blindly.
    pub fn parse<R: io::Read>(reader: &mut R) -> io::Result<Gtid> {
        // Reading and decoding SID
        let mut sid = [0u8; 16];
        reader.read_exact(&mut sid)?;

        // Get the number of interval to read
        let interval_len = read_u64_le(reader)? as usize;

        // TODO: maybe do something to avoid reading an absurd len?
        // Decode the intervals encoded as u64
        let mut intervals = Vec::with_capacity(interval_len.clamp(4, 64));
        for _ in 0..interval_len {
            let start = read_u64_le(reader)?;
            let end = read_u64_le(reader)?;
            intervals.push((start, end))
        }

        // TODO: maybe return an error if not sorted and make a parse_tolerant
        // function?
        // Ensure that we are sorted, it should be the case.
        intervals.sort();
        Ok(Gtid { sid, intervals })
    }

    /// Serialize to binary a [Gtid]
    ///
    /// ## Wire format
    ///
    /// Warning: Subject to change
    ///
    /// Bytes are in **little endian**.
    ///
    /// - `sid`: `16 * u8` as a `[u8;16]`
    /// - `intervals_len`: `8 * u8` as a u64
    ///
    /// `interval_len` times:
    ///     - `start`: `8 * u8` as `u64` start of interval
    ///     - `end`: `8 * u8` as u64 end of interval
    /// ```txt
    /// Aligned on u64 bit
    /// +-+-+-+-+-+-+-+-+-+-+
    /// | sid [16;u8]       |
    /// |                   |
    /// +-+-+-+-+-+-+-+-+-+-+
    /// | intervals_len u64 |
    /// +-+-+-+-+-+-+-+-+-+-+
    /// |start u64              \
    /// - - - - - - - - - - -    + Repeated
    /// |stop u64               /  interval_len
    /// - - - - - - - - - - -      times
    /// ```
    pub fn serialize<W: io::Write>(&self, mut writer: W) -> io::Result<()> {
        // Sid encoded.
        writer.write_all(&self.sid)?;

        // Encode in little endian the len
        writer.write_all(&(self.intervals.len() as u64).to_le_bytes())?;

        // Encode the intervals themselves in little endian (start, stop)
        for (start, end) in self.intervals.iter() {
            writer.write_all(&start.to_le_bytes())?;
            writer.write_all(&end.to_le_bytes())?;
        }
        Ok(())
    }

    /// Release of raw values useful for bridging with `Sid` type in mysql crate.
    pub fn into_raw(self) -> ([u8; 16], Vec<(u64, u64)>) {
        (self.sid, self.intervals)
    }
}

#[inline]
fn overlap(x: &(u64, u64), y: &(u64, u64)) -> bool {
    x.0 < y.1 && x.1 > y.0
}

#[inline]
fn contains(x: &(u64, u64), y: &(u64, u64)) -> bool {
    y.0 >= x.0 && y.1 <= x.1
}

#[inline]
fn read_u64_le<R: io::Read>(reader: &mut R) -> io::Result<u64> {
    let mut buff = [0u8; 8];
    reader.read_exact(&mut buff)?;
    Ok(u64::from_le_bytes(buff))
}

#[derive(Debug, PartialEq, Eq)]
pub enum GtidError {
    /// Sid UUID where not matching
    SidNotMatching,
    /// SID or Interval is in invalid form
    ParseError,
    /// Intervals overlaps
    OverlappingInterval,
    /// Interval must be Ordered (sorted)
    IntervalBadlyOrdered,
    /// Interval shall not contain 0
    ZeroInInterval,
}

impl Error for GtidError {}
impl Display for GtidError {
    /// Return human representation for `GtidError`
    ///
    /// Currently use Debug.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

/// Parse a human-generated interval, end value will be incremented to match mysql internals.
/// Example if given `1,2` will output `(1, 3)`.
///
/// ```ignore
/// # use crate::parse_interval;
/// assert_eq!(parse_interval("1-56"), Ok((1, 56)))
/// ```
fn parse_interval(interval: &str) -> Result<(u64, u64), GtidError> {
    // Nom of the poor.
    let mut iter = interval.split('-');
    let start = iter.next().ok_or(GtidError::ParseError)?;
    let start = start.parse::<u64>().map_err(|_| GtidError::ParseError)?;

    let end = iter.next().map_or_else(
        || Ok(start),
        |end| end.parse::<u64>().map_err(|_| GtidError::ParseError),
    )?;

    if start == 0 || end == 0 {
        return Err(GtidError::ZeroInInterval);
    }
    if start > end {
        return Err(GtidError::IntervalBadlyOrdered);
    }
    Ok((start, end + 1))
}

impl TryFrom<&str> for Gtid {
    /// Parse a GTID from mysql text representation.
    /// TODO fix overeading.
    /// `4350f323-7565-4e59-8763-4b1b83a0ce0e:1-20\n57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56:60-90`
    /// pass and shall not
    fn try_from(gtid: &str) -> Result<Gtid, GtidError> {
        let raw = &gtid.as_bytes().get(0..36).ok_or(GtidError::ParseError)?;
        let sid = parse_uuid(raw)?;

        let rest = &gtid[36..];

        let mut intervals = Vec::new();
        for interval in rest.split(':').skip(1) {
            let interval = parse_interval(interval)?;
            intervals.push(interval);
        }
        intervals.sort();
        if intervals
            .windows(2)
            .any(|tuples| overlap(&tuples[0], &tuples[1]))
        {
            return Err(GtidError::OverlappingInterval);
        }
        Ok(Gtid { sid, intervals })
    }

    type Error = GtidError;
}

/// Returns a UUID from it's binary form
///
/// Panics if binary form is not encodable to ascii.
fn uuid_bin_to_hex(uuid: [u8; 16]) -> [u8; 36] {
    let mut sid_bin = [0u8; 32];

    // decode back to ascii form
    hex::encode_to_slice(uuid, &mut sid_bin).unwrap();

    let mut sid = [0u8; 36];
    let mut writer = &mut sid[..];
    // Inject those annoying as hell '-'
    writer.write_all(&sid_bin[0..8]).unwrap();
    writer.write_all(b"-").unwrap();
    writer.write_all(&sid_bin[8..12]).unwrap();
    writer.write_all(b"-").unwrap();
    writer.write_all(&sid_bin[12..16]).unwrap();
    writer.write_all(b"-").unwrap();
    writer.write_all(&sid_bin[16..20]).unwrap();
    writer.write_all(b"-").unwrap();
    writer.write_all(&sid_bin[20..32]).unwrap();

    // Serve
    sid
}

/// Parses a UUID in the follow form:
/// ```text
/// 3E11FA47-71CA-11E1-9E33-C80AA9429562
/// ```
///
/// Into it's binary condensed representation to be cache friendly.
fn parse_uuid(uuid: &[u8]) -> Result<[u8; 16], GtidError> {
    // Our GTID uuid shall be 32 bytes of Hex and 4 '-'.
    if uuid.len() != 36 {
        return Err(GtidError::ParseError);
    }

    // Assert that we have `-` in the right places.
    match (uuid[8], uuid[13], uuid[18], uuid[23]) {
        (b'-', b'-', b'-', b'-') => {}
        _ => return Err(GtidError::ParseError),
    }

    let mut sid_raw = [0u8; 32];
    let mut writer = &mut sid_raw[..];

    // Skip the '-'
    writer.write_all(&uuid[0..8]).unwrap();
    writer.write_all(&uuid[9..13]).unwrap();
    writer.write_all(&uuid[14..18]).unwrap();
    writer.write_all(&uuid[19..23]).unwrap();
    writer.write_all(&uuid[24..36]).unwrap();

    // If anything is not Hex-digit we fail.
    // Everything is fine let's encode into binary!
    let mut sid = [0u8; 16];
    hex::decode_to_slice(sid_raw, &mut sid).map_err(|_| GtidError::ParseError)?;

    Ok(sid)
}

impl Debug for Gtid {
    /// A representation for debug purpose.
    ///
    /// Considers it not future proof will print something like:
    ///
    /// ```txt
    /// Gtid { sid: "57b70f4e-20d3-11e5-a393-4a63946f7eac", intervals: [ (1, 57), ] }
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO: Test all code-path making GTID to check if path allowing bad utf8 exist.

        // Let get something like
        // 3E11FA47-71CA-11E1-9E33-C80AA9429562
        let sid = uuid_bin_to_hex(self.sid);

        let sid = std::str::from_utf8(&sid).unwrap();
        write!(f, "Gtid {{ sid: \"{sid}\", intervals: [ ")?;
        for interval in self.intervals.iter() {
            write!(f, "{interval:?}, ")?;
        }
        write!(f, "] }}")?;
        Ok(())
    }
}

impl Display for Gtid {
    /// A human friendly representation of a `Gtid`
    ///
    /// Format is still subject to changes.
    ///
    /// ```txt
    /// 57b70f4e-20d3-11e5-a393-4a63946f7eac:1-57:59-61
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO: Test all code-path making GTID to check if path allowing bad utf8 exist.
        let sid = uuid_bin_to_hex(self.sid);
        let sid = std::str::from_utf8(&sid).unwrap();
        write!(f, "{sid}")?;

        for (start, end) in self.intervals.iter() {
            // TODO is it mandatory to do "excluded range" ?
            let end = end - 1;
            if *start == end {
                write!(f, ":{start}")?;
            } else {
                write!(f, ":{start}-{end}")?;
            }
        }
        Ok(())
    }
}

impl PartialOrd for Gtid {
    /// Ordering of GTID follow the following algorithm:
    ///
    /// If UUID are equals:
    ///     Compare intervals
    /// Else ord is based on UUID ordering.
    ///
    /// TODO: Example.
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let ord = self.sid.partial_cmp(&other.sid)?;
        match ord {
            ord @ (Ordering::Less | Ordering::Greater) => Some(ord),
            Ordering::Equal => self.intervals.partial_cmp(&other.intervals),
        }
    }
}

impl Ord for Gtid {
    /// Ordering of GTID follow the following algorithm:
    ///
    /// If UUID are equals:
    ///     Compare intervals
    /// Else ord is based on UUID ordering.
    ///
    /// TODO: Example.
    fn cmp(&self, other: &Self) -> Ordering {
        match self.sid.cmp(&other.sid) {
            ord @ (std::cmp::Ordering::Less | std::cmp::Ordering::Greater) => ord,
            std::cmp::Ordering::Equal => self.intervals.cmp(&other.intervals),
        }
    }
}

#[cfg(test)]
mod test {
    use super::{parse_interval, parse_uuid};
    use crate::{Gtid, GtidError};
    use std::{cmp::Ordering, io::Cursor};

    #[test]
    fn test_parse_interval() {
        assert_eq!(parse_interval("1"), Ok((1, 2)));
        assert_eq!(parse_interval("1-56"), Ok((1, 57)));
        assert_eq!(parse_interval("-1"), Err(GtidError::ParseError));
        assert_eq!(parse_interval("1-"), Err(GtidError::ParseError));
        assert_eq!(parse_interval("0"), Err(GtidError::ZeroInInterval));
        assert_eq!(parse_interval("0-0"), Err(GtidError::ZeroInInterval));
        assert_eq!(parse_interval("0-1"), Err(GtidError::ZeroInInterval));
        assert_eq!(parse_interval("1-0"), Err(GtidError::ZeroInInterval));
        assert_eq!(parse_interval("58-1"), Err(GtidError::IntervalBadlyOrdered));
    }

    #[test]
    fn test_parse_uuid() {
        assert!(parse_uuid(b"57b70f4e-20d3-11e5-a393-4a63946f7eac").is_ok());
        assert!(parse_uuid(b"57B70F4E-20D3-11E5-A393-4A63946F7EAC").is_ok());
        assert_eq!(
            parse_uuid(b"57B70F4E@20D3@11E5@A393-4A63946F7EAC"),
            Err(GtidError::ParseError)
        );
        assert_eq!(
            parse_uuid(b"XXXXXXXX@20D3@11E5@A393-4A63946F7EAC"),
            Err(GtidError::ParseError)
        );
        assert_eq!(
            parse_uuid(b"XXXXXXXX-20D3-11E5-A393-4A63946F7EAC"),
            Err(GtidError::ParseError)
        );
        assert_eq!(parse_uuid(b"XXXXXXXX"), Err(GtidError::ParseError));
        assert_eq!(parse_uuid(b"57B70F4E"), Err(GtidError::ParseError));
        assert_eq!(parse_uuid(b"----"), Err(GtidError::ParseError));
    }

    #[test]
    fn test_parse_gtid() {
        let gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac");
        assert_eq!(
            gtid,
            Gtid::raw_gtid_unchecked(*b"57b70f4e-20d3-11e5-a393-4a63946f7eac")
        );

        let gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56");
        assert_eq!(
            gtid,
            Gtid::with_intervals(*b"57b70f4e-20d3-11e5-a393-4a63946f7eac", vec!((1, 57)))
        );

        let gtid_str = "3e11fa47-71ca-11e1-9e33-c80aa9429562:1-3:11:47-49";
        let gtid = Gtid::try_from(gtid_str).unwrap();
        assert_eq!(gtid_str, gtid.to_string());
    }

    #[test]
    fn test_add_interval() {
        let mut gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        gtid.add_interval(&(58, 60)).unwrap();
        assert_eq!(gtid.intervals, [(1, 57), (58, 60)]);
        gtid.add_interval(&(57, 58)).unwrap();
        assert_eq!(gtid.intervals, [(1, 60)]);
    }

    #[test]
    fn test_add_interval_bad() {
        let mut gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        assert_eq!(gtid.add_interval(&(0, 1)), Err(GtidError::ZeroInInterval));
        assert_eq!(
            gtid.add_interval(&(59, 51)),
            Err(GtidError::IntervalBadlyOrdered)
        );

        assert_eq!(
            gtid.add_interval(&(50, 51)),
            Err(GtidError::OverlappingInterval)
        );

        assert_eq!(gtid.intervals, [(1, 57)]);
    }

    #[test]
    fn test_sub_interval_begin() {
        let mut gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        // Begin
        gtid.sub_interval(&(1, 2)).unwrap();
        assert_eq!(gtid.intervals, [(2, 57)],);
    }

    #[test]
    fn test_sub_interval_within() {
        let mut gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        // Begin
        gtid.sub_interval(&(25, 26)).unwrap();
        assert_eq!(gtid.intervals, [(1, 25), (26, 57)],);
    }

    #[test]
    fn test_sub_interval_end() {
        let mut gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        gtid.sub_interval(&(50, 57)).unwrap();
        assert_eq!(gtid.intervals, [(1, 50)],);
    }

    #[test]
    fn test_sub_interval_bad() {
        let mut gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        assert_eq!(gtid.sub_interval(&(0, 1)), Err(GtidError::ZeroInInterval));
        assert_eq!(
            gtid.sub_interval(&(59, 51)),
            Err(GtidError::IntervalBadlyOrdered)
        );
    }

    #[test]
    fn test_sub_interval_nothing_not_overlap() {
        let mut gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        assert_eq!(gtid.sub_interval(&(0, 1)), Err(GtidError::ZeroInInterval));
        assert_eq!(gtid.sub_interval(&(60, 70)), Ok(()));
        assert_eq!(gtid.intervals, [(1, 57)],);
    }

    #[test]
    fn test_include_interval() {
        let mut gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        let other = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:58-59").unwrap();
        gtid.include_transactions(&other).unwrap();
        assert_eq!(gtid.intervals, [(1, 57), (58, 60)])
    }

    #[test]
    fn test_remove_interval_end() {
        // Remove inside
        let mut gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        let other = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:56").unwrap();
        gtid.remove_transactions(&other).unwrap();
        assert_eq!(gtid.intervals, [(1, 56)]);
    }

    #[test]
    fn test_remove_interval_start() {
        // begin inside
        let mut gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        let other = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1").unwrap();
        gtid.remove_transactions(&other).unwrap();
        assert_eq!(gtid.intervals, [(2, 57)]);
    }

    #[test]
    fn test_remove_interval_within() {
        // Check with python.
        let mut gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        let other = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:25").unwrap();
        gtid.remove_transactions(&other).unwrap();
        assert_eq!(gtid.intervals, [(1, 25), (26, 57)]);
    }

    #[test]
    fn test_remove_bad_sid() {
        // Check with python.
        let mut gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        let other = Gtid::try_from("deadbeef-20d3-11e5-a393-4a63946f7eac:25").unwrap();
        assert_eq!(
            gtid.remove_transactions(&other),
            Err(GtidError::SidNotMatching)
        );
        assert_eq!(gtid.intervals, [(1, 57)]);
    }

    #[test]
    fn test_include_interval_fail() {
        let mut gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        let other = Gtid::try_from("deadbeef-cafe-baba-abab-bad3946f7eac:58-59").unwrap();
        assert_eq!(
            gtid.include_transactions(&other),
            Err(GtidError::SidNotMatching)
        );
    }

    #[test]
    fn test_encode_decode() {
        let gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56:59-69").unwrap();
        let mut buffer = Vec::with_capacity(64);
        gtid.serialize(&mut buffer).unwrap();
        let decoded = Gtid::parse(&mut Cursor::new(buffer)).unwrap();
        assert_eq!(decoded, gtid);
    }

    #[test]
    fn test_contains() {
        let gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        let other = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:5-10").unwrap();

        assert!(gtid.contains(&other));
        assert!(!other.contains(&gtid));
    }

    #[test]
    fn test_contains_not_same_sid() {
        let gtid = Gtid::try_from("deadbeef-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        let other = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:5-10").unwrap();

        assert!(!gtid.contains(&other));
    }

    #[test]
    fn test_ordering() {
        let gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        let other = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:5-10").unwrap();
        assert!(gtid.lt(&other));
        assert!(gtid.le(&other));
        assert!(!gtid.gt(&other));
        assert!(!gtid.ge(&other));
        let other = Gtid::try_from("deadbeef-20d3-11e5-a393-4a63946f7eac:5-10").unwrap();
        assert!(gtid.le(&other));
        assert!(!gtid.ge(&other));
        assert!(gtid.lt(&other));
        assert!(!gtid.gt(&other));

        let gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        let other = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        assert!(gtid.eq(&other));
        assert!(!gtid.lt(&other));
        assert!(gtid.le(&other));
        assert!(!gtid.gt(&other));
        assert!(gtid.ge(&other));

        let other = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac").unwrap();
        assert!(!gtid.eq(&other));

        let other = Gtid::try_from("deadbeef-20d3-11e5-a393-4a63946f7eac").unwrap();
        assert!(!gtid.eq(&other));
    }

    #[test]
    fn test_ord() {
        let gtid = Gtid::try_from("0Ab70f4e-20d3-11e5-a393-4a63946f7eac").unwrap();
        let other = Gtid::try_from("1Aadbeef-20d3-11e5-a393-4a63946f7eac").unwrap();
        assert_eq!(gtid.cmp(&other), Ordering::Less);
        assert_eq!(other.cmp(&gtid), Ordering::Greater);
        assert_eq!(gtid.cmp(&gtid.clone()), Ordering::Equal);

        let gtid = Gtid::try_from("0Ab70f4e-20d3-11e5-a393-4a63946f7eac:1-5").unwrap();
        let other = Gtid::try_from("0Ab70f4e-20d3-11e5-a393-4a63946f7eac:6-10").unwrap();
        assert_eq!(gtid.cmp(&other), Ordering::Less);
        assert_eq!(other.cmp(&gtid), Ordering::Greater);
    }

    #[test]
    fn test_display_debug() {
        let gtid_string = "57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56:58-60";
        let gtid = Gtid::try_from(gtid_string).unwrap();

        assert_eq!(gtid_string, gtid.to_string());
        let debug = format!("{gtid:?}");
        assert_eq!("Gtid { sid: \"57b70f4e-20d3-11e5-a393-4a63946f7eac\", intervals: [ (1, 57), (58, 61), ] }", debug);
    }

    #[test]
    fn test_parse_fail() {
        let gtids = "-";
        assert!(Gtid::try_from(gtids).is_err());
        let gtids =
        "4350f323-7565-4e59-8763-4b1b83a0ce0e:1-20\n57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56:60-90";
        assert!(Gtid::try_from(gtids).is_err());
    }

    #[test]
    fn test_parse_strict() {
        let gtids = "57b70f4e-20d3-11e5-a393-4a63946f7eac:0-1";
        assert_eq!(Gtid::try_from(gtids), Err(GtidError::ZeroInInterval));
        let gtids = "4350f323-7565-4e59-8763-4b1b83a0ce0e:20-1";
        assert_eq!(Gtid::try_from(gtids), Err(GtidError::IntervalBadlyOrdered));

        let gtids = "57b70f4e-20d3-11e5-a393-4a63946f7eac:1-5:2-3";
        assert_eq!(Gtid::try_from(gtids), Err(GtidError::OverlappingInterval));
    }
}
