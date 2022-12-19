// Author Axel Viala <axel.viala@darnuria.eu>
// Done on free time inspired a lot by pymysqlreplication own implementation.
// Licence MIT + APACHE 2.

use std::collections::HashMap;

use crate::Gtid;

#[derive(Debug, PartialEq, Eq)]
pub struct GtidSet {
    /// Key: Sid + Gno value Gtid
    /// TODO only keep Intervals in value.
    gtids: HashMap<[u8; 16], Gtid>,
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
        let gtids: HashMap<[u8; 16], Gtid> = HashMap::with_capacity(array.len());
        let mut gtids = GtidSet { gtids };
        for gtid in array {
            gtids.include_gtid(gtid);
        }
        gtids
    }
}

impl GtidSet {
    pub fn include_gtid(&mut self, gtid: &Gtid) {
        match self.gtids.get_mut(&gtid.sid_gno) {
            // Unwraping is safe we work on the same sid-gno.
            Some(g) => g.include_transactions(gtid).unwrap(),
            None => {
                self.gtids.insert(gtid.sid_gno, gtid.clone());
            }
        }
    }

    pub fn contains_gtid(&self, gtid: &Gtid) -> bool {
        match self.gtids.get(&gtid.sid_gno) {
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
}
