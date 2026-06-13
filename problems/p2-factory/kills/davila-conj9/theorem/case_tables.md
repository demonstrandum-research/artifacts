### Block `mid`, grants R = {s_in,s_out}, start sets of size 1 (orbit representatives; group order 4)

| representative X | orbit size | stalled closure of X ∪ R | surviving fort F = V ∖ closure |
|---|---|---|---|
| {a1} | 4 | {a1,b1,s_in,s_out} | {a2,a3,b2,b3} |
| {a3} | 2 | {a3,s_in,s_out} | {a1,a2,b1,b2,b3} |

### Block `mid`, grants R = {s_in}, start sets of size 2 (orbit representatives; group order 2)

| representative X | orbit size | stalled closure of X ∪ R | surviving fort F = V ∖ closure |
|---|---|---|---|
| {a1,a2} | 2 | {a1,a2,a3,b1,s_in} | {b2,b3,s_out} |
| {a1,a3} | 2 | {a1,a2,a3,b1,s_in} | {b2,b3,s_out} |
| {a1,b1} | 1 | {a1,b1,s_in} | {a2,a3,b2,b3,s_out} |
| {a1,b2} | 2 | {a1,b1,b2,b3,s_in} | {a2,a3,s_out} |
| {a1,b3} | 2 | {a1,b1,b2,b3,s_in} | {a2,a3,s_out} |
| {a2,a3} | 2 | {a2,a3,s_in} | {a1,b1,b2,b3,s_out} |
| {a2,b2} | 1 | {a2,b2,s_in} | {a1,a3,b1,b3,s_out} |
| {a2,b3} | 2 | {a2,b3,s_in} | {a1,a3,b1,b2,s_out} |
| {a3,b3} | 1 | {a3,b3,s_in} | {a1,a2,b1,b2,s_out} |

### Block `mid`, grants R = {}, start sets of size 3 (orbit representatives; group order 4)

| representative X | orbit size | stalled closure of X ∪ R | surviving fort F = V ∖ closure |
|---|---|---|---|
| {a1,a2,a3} | 2 | {a1,a2,a3} | {b1,b2,b3,s_in,s_out} |
| {a1,a2,b1} | 4 | {a1,a2,b1} | {a3,b2,b3,s_in,s_out} |
| {a1,a2,b3} | 2 | {a1,a2,a3,b3} | {b1,b2,s_in,s_out} |
| {a1,a3,b1} | 4 | {a1,a3,b1} | {a2,b2,b3,s_in,s_out} |
| {a1,a3,b2} | 4 | {a1,a2,a3,b2,s_out} | {b1,b3,s_in} |
| {a1,a3,b3} | 4 | {a1,a2,a3,b3} | {b1,b2,s_in,s_out} |

### Block `end`, grants R = {s}, start sets of size 2 (orbit representatives; group order 8)

| representative X | orbit size | stalled closure of X ∪ R | surviving fort F = V ∖ closure |
|---|---|---|---|
| {a1,a2} | 4 | {a1,a2,a3,b1,s} | {b2,b3} |
| {a1,b1} | 1 | {a1,b1,s} | {a2,a3,b2,b3} |
| {a1,b2} | 4 | {a1,b1,b2,b3,s} | {a2,a3} |
| {a2,a3} | 2 | {a2,a3,s} | {a1,b1,b2,b3} |
| {a2,b2} | 4 | {a2,b2,s} | {a1,a3,b1,b3} |

### Block `end`, grants R = {}, start sets of size 3 (orbit representatives; group order 8)

| representative X | orbit size | stalled closure of X ∪ R | surviving fort F = V ∖ closure |
|---|---|---|---|
| {a1,a2,a3} | 2 | {a1,a2,a3} | {b1,b2,b3,s} |
| {a1,a2,b1} | 4 | {a1,a2,b1} | {a3,b2,b3,s} |
| {a1,a2,b2} | 8 | {a1,a2,a3,b2} | {b1,b3,s} |
| {a1,b2,b3} | 2 | {a1,b1,b2,b3,s} | {a2,a3} |
| {a2,a3,b2} | 4 | {a1,a2,a3,b2} | {b1,b3,s} |
