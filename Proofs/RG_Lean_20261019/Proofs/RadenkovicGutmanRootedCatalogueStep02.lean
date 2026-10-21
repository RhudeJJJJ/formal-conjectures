/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanRootedCatalogueData
namespace Gebendorfer.RadenkovicGutman.RootedCatalogueData
open RootedTreeEnumeration CanonicalTreeCoverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def witnesses2 : Fin level2.length → Vertices 2 → Witness 3 level3.length :=
  fun i v => ![![{target := ⟨2,by decide⟩,map := fun x => ![(some (some (some ()))),(some (some none)),(some none),none] (label x)},{target := ⟨1,by decide⟩,map := fun x => ![(some (some (some ()))),(some (some none)),(some none),none] (label x)},{target := ⟨0,by decide⟩,map := fun x => ![(some (some (some ()))),(some (some none)),(some none),none] (label x)}],![{target := ⟨3,by decide⟩,map := fun x => ![(some (some (some ()))),(some (some none)),(some none),none] (label x)},{target := ⟨2,by decide⟩,map := fun x => ![(some (some (some ()))),(some (some none)),none,(some none)] (label x)},{target := ⟨2,by decide⟩,map := fun x => ![(some (some (some ()))),none,(some (some none)),(some none)] (label x)}]] i (label v)
theorem step2 : checkStep 2 level2 level3 witnesses2=true := by decide +kernel
#print axioms step2
end Gebendorfer.RadenkovicGutman.RootedCatalogueData
