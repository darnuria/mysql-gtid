// Author Axel Viala <axel.viala@darnuria.eu>
// Done on free time inspired a lot by pymysqlreplication own implementation.
// Licence MIT + APACHE 2.

use std::io::Write;
use std::{
    error::Error,
    fmt::{Debug, Display},
    io,
};

/// Get a regex initialized once.
/// from https://docs.rs/once_cell/latest/once_cell/
macro_rules! regex {
    ($re:literal $(,)?) => {{
        static RE: once_cell::sync::OnceCell<regex::Regex> = once_cell::sync::OnceCell::new();
        RE.get_or_init(|| regex::Regex::new($re).expect("Unable to compile regex."))
    }};
}

#[derive(PartialEq, Eq)]
pub struct Gtid {
    sid_gno: [u8; 36], // 32 + 4 '-'
    intervals: Vec<(u64, u64)>,
}

impl Gtid {
    pub fn raw_gtid_unchecked(sid_gno: [u8; 36]) -> Gtid {
        Gtid {
            sid_gno,
            intervals: vec![],
        }
    }

    pub fn with_intervals(sid_gno: [u8; 36], intervals: Vec<(u64, u64)>) -> Gtid {
        let mut intervals = intervals;
        intervals.sort();
        Gtid { sid_gno, intervals }
    }

    fn add_interval(&mut self, interval: (u64, u64)) -> Result<(), GtidError> {
        if interval.0 > interval.1 {
            return Err(GtidError::IntervalBadlyOrdered);
        }

        if self.intervals.iter().any(|&x| overlap(x, interval)) {
            return Err(GtidError::OverlapingInterval);
        }

        let mut interval = interval;
        self.intervals.sort();
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
        Ok(())
    }

    /// Remove an interval from intervals.
    pub fn sub_interval(&mut self, interval: (u64, u64)) -> Result<(), GtidError> {
        if interval.0 > interval.1 {
            return Err(GtidError::IntervalBadlyOrdered);
        }

        // Nothing to do in this case.
        if !self.intervals.iter().any(|&x| overlap(x, interval)) {
            return Ok(());
        }

        self.intervals.sort();
        // TODO: Do it in place with a filter.
        let mut new: Vec<(u64, u64)> = Vec::with_capacity(self.intervals.len());
        for current in self.intervals.iter() {
            if overlap(*current, interval) {
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
        Ok(())
    }

    pub fn contains(&self, other: &Gtid) -> bool {
        if self.sid_gno != other.sid_gno {
            return false;
        }

        other
            .intervals
            .iter()
            .all(|them| self.intervals.iter().any(|me| contains(*me, *them)))
    }

    /// Merge two transactions interval
    pub fn include_transaction(mut self, other: Gtid) -> Result<Gtid, GtidError> {
        if self.sid_gno != other.sid_gno {
            return Err(GtidError::SidNotMatching);
        }

        for interval in other.intervals {
            self.add_interval(interval)?;
        }

        Ok(self)
    }

    pub fn parse<R: io::Read>(mut reader: R) -> io::Result<Gtid> {
        // Reading and decoding SID+GNO
        let mut sid_gno = [0u8; 16];
        reader.read_exact(&mut sid_gno)?;
        let mut out = [0u8; 32];
        hex::encode_to_slice(sid_gno, &mut out).map_err(|_| io::ErrorKind::InvalidInput)?;
        let mut sid_gno = [0u8; 36];
        let mut writer = &mut sid_gno[..];
        writer.write(&out[0..8])?;
        writer.write(b"-")?;
        writer.write(&out[8..12])?;
        writer.write(b"-")?;
        writer.write(&out[12..16])?;
        writer.write(b"-")?;
        writer.write(&out[16..20])?;
        writer.write(b"-")?;
        writer.write(&out[20..32])?;

        let mut interval_len = [0u8; 8];
        reader.read_exact(&mut interval_len)?;
        let interval_len = u64::from_le_bytes(interval_len) as usize;

        let mut intervals = Vec::with_capacity(interval_len.clamp(4, 64));
        for _ in 0..interval_len {
            let mut start = [0u8; 8];
            reader.read_exact(&mut start)?;
            let start = u64::from_le_bytes(start);
            let mut end = [0u8; 8];
            reader.read_exact(&mut end)?;
            let end = u64::from_le_bytes(end);
            intervals.push((start, end))
        }
        Ok(Gtid::with_intervals(sid_gno, intervals))
    }

    pub fn serialize<W: io::Write>(&self, mut writer: W) -> io::Result<()> {
        // TODO: Plz remove those `-` in constructor :facepalm:
        let sid_gno: [u8; 32] = self
            .sid_gno
            .iter()
            .filter(|&&c| c != b'-')
            .copied()
            .collect::<Vec<u8>>()
            .try_into()
            .unwrap();

        let mut sid_gno_bin = [0u8; 16];
        hex::decode_to_slice(sid_gno, &mut sid_gno_bin).map_err(|_| io::ErrorKind::InvalidInput)?;

        // Sid+gno encoded.
        writer.write(&sid_gno_bin)?;

        // Encode in little endian the len
        writer.write(&(self.intervals.len() as u64).to_le_bytes())?;

        // Encode the intervals itselfs in little endian (start, stop)
        for (start, end) in self.intervals.iter() {
            writer.write(&start.to_le_bytes())?;
            writer.write(&end.to_le_bytes())?;
        }
        Ok(())
    }
}

#[inline]
fn overlap(x: (u64, u64), y: (u64, u64)) -> bool {
    x.0 < y.1 && x.1 > y.0
}

#[inline]
fn contains(x: (u64, u64), y: (u64, u64)) -> bool {
    y.0 >= x.0 && y.1 <= x.1
}

#[derive(Debug, PartialEq)]
pub enum GtidError {
    SidNotMatching,
    ParseError,
    OverlapingInterval,
    IntervalBadlyOrdered,
}

impl Error for GtidError {}
impl Display for GtidError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

/// Parse a human-generated interval, end value will be incremented to match mysql internals.
/// Exemple if given `1,2` will output `(1, 3)`.
///
/// ```ignore
/// # use parse_interval;
/// let interval = parse_interval("1-56").unwrap()
/// assert_eq!(interval, (1, 56))
/// ```
/// TODO work without regex.
/// TODO: Think about using range.
fn parse_interval(interval: &str) -> Result<(u64, u64), GtidError> {
    let re = regex!("^([0-9]+)(?:-([0-9]+))?$");
    let cap = re.captures(interval).ok_or(GtidError::ParseError)?;

    // already checked that it's only number above.
    let start = cap.get(1).unwrap().as_str().parse::<u64>().unwrap();
    let end = cap.get(2).map_or_else(
        || start,
        |interval| interval.as_str().parse::<u64>().unwrap(),
    );
    Ok((start, end + 1))
}

impl TryFrom<&str> for Gtid {
    /// Parse a GTID from mysql text representation.
    /// TODO: Pass to nom.
    fn try_from(gtid: &str) -> Result<Gtid, GtidError> {
        let re = regex!("^([0-9a-fA-F]{8}(?:-[0-9a-fA-F]{4}){3}-[0-9a-fA-F]{12})((:?:[0-9-]+)+)?$");
        let cap = re.captures(gtid).ok_or(GtidError::ParseError)?;
        let sid_gno = cap.get(1).unwrap().as_str().as_bytes();
        let intervals = cap.get(2).map_or_else(Vec::new, |intervals| {
            intervals
                .as_str()
                .split(':')
                .skip(1)
                .filter_map(|x| parse_interval(x).ok())
                .collect::<Vec<_>>()
        });

        // already checked in regex.
        Ok(Gtid::with_intervals(
            <[u8; 36]>::try_from(sid_gno).unwrap(),
            intervals,
        ))
    }

    type Error = GtidError;
}

impl Debug for Gtid {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO: Test all code-path making GTID to check if path allowing bad utf8 exist.
        let sid_gno = std::str::from_utf8(&self.sid_gno).unwrap();
        write!(f, "Gtid {{ sid_gno: \"{}\", intervals: [ ", sid_gno)?;
        for interval in self.intervals.iter() {
            write!(f, "{:?}, ", interval)?;
        }
        write!(f, "] }}")?;
        Ok(())
    }
}

impl Display for Gtid {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO: Test all code-path making GTID to check if path allowing bad utf8 exist.
        let sid_gno = std::str::from_utf8(&self.sid_gno).unwrap();
        write!(f, "{}", sid_gno)?;

        let len = self.intervals.len();
        for (n, (start, end)) in self.intervals.iter().enumerate() {
            // TODO is it mandatory to do "excluded range" ?
            write!(f, "{}-{}", start, end - 1)?;
            if n != len - 1 {
                write!(f, ":")?
            }
        }
        Ok(())
    }
}

struct GtidSet {}

#[cfg(test)]
mod test {
    use std::io::Cursor;

    use crate::Gtid;

    use super::parse_interval;

    #[test]
    fn test_parse_interval() {
        let interval = parse_interval("1-56").unwrap();
        assert_eq!(interval, (1, 57));
        let interval = parse_interval("1").unwrap();
        assert_eq!(interval, (1, 2));
    }

    #[test]
    fn test_parse_gtid() {
        let gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac").unwrap();
        assert_eq!(
            gtid,
            Gtid::raw_gtid_unchecked(*b"57b70f4e-20d3-11e5-a393-4a63946f7eac")
        );

        let gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        assert_eq!(
            gtid,
            Gtid::with_intervals(*b"57b70f4e-20d3-11e5-a393-4a63946f7eac", vec!((1, 57)))
        );
    }

    #[test]
    fn test_add_interval() {
        let mut gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        gtid.add_interval((58, 60)).unwrap();
        assert_eq!(gtid.intervals, [(1, 57), (58, 60)]);
        gtid.add_interval((57, 58)).unwrap();
        assert_eq!(gtid.intervals, [(1, 60)]);
    }

    #[test]
    fn test_include_interval() {
        let gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        let other = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:58-59").unwrap();
        let gtid = gtid.include_transaction(other).unwrap();
        assert_eq!(gtid.intervals, [(1, 57), (58, 60)])
    }

    #[test]
    fn test_encode_decode() {
        let gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        let mut buffer = Vec::with_capacity(64);
        gtid.serialize(&mut buffer).unwrap();
        let decoded = Gtid::parse(Cursor::new(buffer)).unwrap();
        assert_eq!(decoded, gtid)
    }

    #[test]
    fn test_contains() {
        let gtid = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap();
        let other = Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:5-10").unwrap();

        assert!(gtid.contains(&other));
        assert!(!other.contains(&gtid));
    }
}
