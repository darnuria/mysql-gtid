// Author Axel Viala <axel.viala@darnuria.eu>
// Done on free time inspired a lot by pymysqlreplication own implementation.
// Licence MIT + APACHE 2.

use std::{collections::BTreeMap, fmt::Display};

use crate::{Gtid, GtidError};

/// A GTIDSet consist of a set of single GTID or ranges of multiples `GTID`.
///
/// Note:
/// When GTID sets are returned from server variables,
/// UUIDs are in alphabetical order, and numeric intervals are merged and in ascending order.
///
/// It's preserved for printing purpose.
#[derive(Debug, PartialEq, Eq)]
pub struct GtidSet {
    /// Key: Sid value Gtid
    /// TODO only keep Intervals in value.
    gtids: BTreeMap<[u8; 16], Gtid>,
}

impl Default for GtidSet {
    /// Construct the Empty GtidSet
    fn default() -> Self {
        Self {
            gtids: Default::default(),
        }
    }
}

impl From<&[Gtid]> for GtidSet {
    fn from(array: &[Gtid]) -> GtidSet {
        let gtids: BTreeMap<[u8; 16], Gtid> = BTreeMap::new();
        let mut gtids = GtidSet { gtids };
        for gtid in array {
            gtids.include_gtid(gtid);
        }
        gtids
    }
}

impl GtidSet {
    pub fn include_gtid(&mut self, gtid: &Gtid) {
        match self.gtids.get_mut(&gtid.sid) {
            // Unwraping is safe we work on the same sid
            Some(g) => g.include_transactions(gtid).unwrap(),
            None => {
                self.gtids.insert(gtid.sid, gtid.clone());
            }
        }
    }

    pub fn include_gtid_consume(&mut self, gtid: Gtid) {
        match self.gtids.get_mut(&gtid.sid) {
            // Unwraping is safe we work on the same sid
            Some(g) => g.include_transactions(&gtid).unwrap(),
            None => {
                self.gtids.insert(gtid.sid, gtid);
            }
        }
    }

    pub fn contains_gtid(&self, gtid: &Gtid) -> bool {
        match self.gtids.get(&gtid.sid) {
            Some(found) => found.contains(gtid),
            None => false,
        }
    }

    pub fn contains_gtidset(&self, gtid: &GtidSet) -> bool {
        gtid.gtids
            .iter()
            .all(|(_, value)| self.contains_gtid(value))
    }

    pub fn merge(&mut self, other: &GtidSet) {
        for g in other.gtids.values() {
            self.include_gtid(g);
        }
    }
}

impl Display for GtidSet {
    /// A human friendly representation of a `GtidSet`. It's a separated by comma list of Gtid.
    ///
    /// Format is still subject to changes.
    ///
    /// ```txt
    /// 57b70f4e-20d3-11e5-a393-4a63946f7eac:1-57, 4350f323-7565-4e59-8763-4b1b83a0ce0e:1-20"
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let len = self.gtids.len();
        for (i, gtid) in self.gtids.values().enumerate() {
            if i != len - 1 {
                write!(f, "{gtid},")?;
            } else {
                write!(f, "{gtid}")?;
            }
        }
        Ok(())
    }
}

impl TryFrom<&str> for GtidSet {
    /// Parse a GtidSet from mysql text representation with or without newline.
    /// Todo use nom?
    /// TODO fix overeading.
    /// `4350f323-7565-4e59-8763-4b1b83a0ce0e:1-20\n57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56:60-90`
    /// pass and shall not
    fn try_from(gtid_set: &str) -> Result<GtidSet, GtidError> {
        let mut gtids = GtidSet {
            gtids: BTreeMap::new(),
        };

        for gtid in gtid_set.split(',') {
            // Don't care for space or \n.
            let gtid = gtid.trim_matches(|c| c == ' ' || c == '\n');
            let end = gtid.len();
            let end = if gtid.ends_with(',') { end - 1 } else { end };
            let gtid = Gtid::try_from(&gtid[..end])?;
            gtids.include_gtid_consume(gtid);
        }

        Ok(gtids)
    }

    type Error = GtidError;
}

#[cfg(test)]
mod test {
    use crate::Gtid;

    use super::GtidSet;

    #[test]
    fn test_include_interval() {
        let gtid_array = [
            Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56").unwrap(),
            Gtid::try_from("deadbeef-20d3-11e5-a393-4a63946f7eac:1-56").unwrap(),
            Gtid::try_from("deadbeef-20d3-11e5-a393-4a63946f7eac:57-59").unwrap(),
        ];
        let gtids = GtidSet::try_from(&gtid_array[..]).unwrap();
        assert!(gtids
            .contains_gtid(&Gtid::try_from("deadbeef-20d3-11e5-a393-4a63946f7eac:57-59").unwrap()));
        assert!(gtids
            .contains_gtid(&Gtid::try_from("deadbeef-20d3-11e5-a393-4a63946f7eac:1-2").unwrap()));
        assert!(!gtids
            .contains_gtid(&Gtid::try_from("deadbeef-20d3-11e5-a393-4a63946f7eac:60-99").unwrap()));
    }

    #[test]
    fn test_display() {
        let gtids =
            "4350f323-7565-4e59-8763-4b1b83a0ce0e:1-20,57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56:60-90";
        let gtid_array = [
            Gtid::try_from("4350f323-7565-4e59-8763-4b1b83a0ce0e:1-20").unwrap(),
            Gtid::try_from("57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56:60-90").unwrap(),
        ];
        let text_rpz = GtidSet::try_from(&gtid_array[..]).unwrap().to_string();
        assert_eq!(text_rpz, gtids);
    }

    #[test]
    fn test_parse_alone() {
        let gtids = "57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56:60-90";
        let text_rpz = GtidSet::try_from(gtids).unwrap().to_string();
        assert_eq!(text_rpz, gtids);
    }
    #[test]

    fn test_parse_multiples() {
        let gtids =
            "4350f323-7565-4e59-8763-4b1b83a0ce0e:1-20,57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56:60-90";
        let text_rpz = GtidSet::try_from(gtids).unwrap().to_string();
        assert_eq!(text_rpz, gtids);
    }

    #[test]
    fn test_parse_newline() {
        let gtids =
        "4350f323-7565-4e59-8763-4b1b83a0ce0e:1-20,\n57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56:60-90";
        let text_rpz = GtidSet::try_from(gtids).unwrap().to_string();
        assert_eq!(text_rpz, "4350f323-7565-4e59-8763-4b1b83a0ce0e:1-20,57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56:60-90");
    }

    #[test]
    #[ignore = "Fix overeading"]
    fn test_parse_fail() {
        let gtids =
        "-";
        assert!(GtidSet::try_from(gtids).is_err());
        let gtids =
        "4350f323-7565-4e59-8763-4b1b83a0ce0e:1-20\n57b70f4e-20d3-11e5-a393-4a63946f7eac:1-56:60-90";
        assert!(dbg!(GtidSet::try_from(gtids)).is_err());
    }
}
