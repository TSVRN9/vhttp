# Requirements (gate-demos fixture for scripts/requirements.sh)

## RFC 1

| § | Topic | #MUST/MUST NOT | Server applies? | Phase | Notes | Status |
|---|---|---|---|---|---|---|
| 1 | proved | 1 | yes | 2 | ✅ done | proved:good_fn |
| 2 | client rule | 1 | no | N/A (client-only) | | n/a |
| 3 | declined feature | 1 | no | Declined (optional: X) | | declined |
| 4 | tested only | 1 | yes | 2 | pinned by a test | tested:good_test; open:2 |
| 5 | known false | 1 | yes | 2 | false today | false (t2); open:2 |
| 6 | half proved | 1 | yes | 2 | detection proved | proved:good_fn; open:2 |
