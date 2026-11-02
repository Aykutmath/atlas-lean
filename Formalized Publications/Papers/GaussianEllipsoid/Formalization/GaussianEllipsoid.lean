/-
# GaussianEllipsoid formalization — library root

Atlas-style layout: `Formalization/` holds the frozen 770-module
development unchanged (`GaussianEllipsoid/` paper-facing modules and
`GaussianEllipsoidNative/` backend modules), and this file is the
paper-order entry point. Paper correspondence and build instructions:
see `../Readme.md`; the interactive paper rendering is
`../Papers/gaussian_ellipsoid_interactive.html`.

Namespaces inside the moved files are unchanged (`GaussianEllipsoid`,
`AHHGaussian`, `AHHRadial`, `AHHAlgebraBridges`, …), so
fully-qualified theorem names are exactly as checked; only the package
prefix (`Formalization/`) reflects the new layout. No statement was
weakened, no hypothesis added, no proof replaced.

The unconditional endpoint is
`GaussianEllipsoid.strict_threshold_unconditional`
(`GaussianEllipsoidNative/StrictThresholdProjectFinal.lean`),
of type `GaussianEllipsoid.StrictThresholdStatement`
(`GaussianEllipsoid/PaperMain.lean`).

Known layout edge (documented, checked): the backend modules import
each other by bare module name under the `GaussianEllipsoidNative`
library root (see the source project's `lakefile.toml`), while the
paper-facing modules import by `GaussianEllipsoid.*` path; both
resolve inside `Formalization/` exactly as in the source project.
-/

-- Paper statements (Theorem 1.1 targets) and the conditional assembly
import GaussianEllipsoid.PaperMain
import GaussianEllipsoid.StrictThreshold

-- Unconditional discharge: below/above threads and the conic bound
import StrictThresholdProjectFinal
import BelowThresholdProjectFinal
import UniformConicBoundUnconditional
