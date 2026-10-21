/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanRootedCatalogueData
namespace Gebendorfer.RadenkovicGutman.RootedCatalogueData
open RootedTreeEnumeration CanonicalTreeCoverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def witnesses1 : Fin level1.length → Vertices 1 → Witness 2 level2.length :=
  fun i v => ![![({target := ⟨1,by decide⟩,map := fun x => ![(some (some ())),(some none),none] (label x)} : Witness 2 level2.length),({target := ⟨0,by decide⟩,map := fun x => ![(some (some ())),(some none),none] (label x)} : Witness 2 level2.length)]] i (label v)
theorem step1 : checkStep 1 level1 level2 witnesses1=true := by decide +kernel
#print axioms step1
end Gebendorfer.RadenkovicGutman.RootedCatalogueData
