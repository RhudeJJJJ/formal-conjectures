/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanRootedCatalogueData
namespace Gebendorfer.RadenkovicGutman.RootedCatalogueData
open RootedTreeEnumeration CanonicalTreeCoverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def witnesses0 : Fin level0.length → Vertices 0 → Witness 1 level1.length :=
  fun i v => ![![({target := ⟨0,by decide⟩,map := fun x => ![(some ()),none] (label x)} : Witness 1 level1.length)]] i (label v)
theorem step0 : checkStep 0 level0 level1 witnesses0=true := by decide +kernel
#print axioms step0
end Gebendorfer.RadenkovicGutman.RootedCatalogueData
