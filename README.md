## Mysql GTID manipulation

[![Rust](https://github.com/darnuria/mysql-gtid/actions/workflows/rust.yml/badge.svg)](https://github.com/darnuria/mysql-gtid/actions/workflows/rust.yml)

Heavily inspired by [Python-mysql-replication](https://github.com/julien-duponchelle/python-mysql-replication/blob/main/pymysqlreplication/gtid.py).
If I found some better implementation or algorithm or test I will contribute it
back there.

I would rather suggest to wait before putting that in production I Intend to to
a lot of testing about and improve some bits.

## Current state

Toy project but somewhat usable.

## Objectives

- No crash in lib
- Mostly all the API of py-mysql-replication except the liberal in what they
  accept constructor
- Try to integrate with mysql rust lib.
- Do a little bit of CI.
- Have for manimulating GTID:
  - [x] an inplace API
  - [ ] copy API

## Context

Began it on freetime due to frustration with a problem my work at
[gandi.net](https://gandi.net).  For now work on that on my freetime.

## License

Apache V2.0 / MIT
