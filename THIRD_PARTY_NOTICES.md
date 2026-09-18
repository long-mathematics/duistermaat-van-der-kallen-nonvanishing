# Third-party proof code

`DuistermaatVanDerKallen/ODEContinuation.lean` contains modified proofs from
mathlib at revision `5ed2965256430c3649e86755f9576b54eca72435`:

- `Mathlib/Analysis/ODE/ExistUnique.lean`: Copyright (c) 2026 Winston Yin.
- `Mathlib/Analysis/ODE/PicardLindelof.lean`: Copyright (c) 2021 Yury Kudryashov;
  authors Yury Kudryashov and Winston Yin.

The local Picard construction was modified to retain its range bound and to
supply uniform local existence inside a prescribed open domain. Additional
project proofs establish compact-domain continuation and finite-time existence
from a priori control. This module is distributed under the
[Apache License 2.0](LICENSES/Apache-2.0.txt), rather than the repository's default
MIT license. The upstream copyright notices are retained in the module.
