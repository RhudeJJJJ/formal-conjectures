/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4040 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap4040 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,11,5,6,7,8,9,10] (sourceLabel 5 2 2 v)
def fusedMap4040 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 2 2 v)
theorem sourceMap4040_checked : acceptsGraphIso
    (source (graph core4040) (root 5) 2 2) DegreeOneSmallSpectrum816.graph sourceMap4040=true := by decide +kernel
theorem fusedMap4040_checked : acceptsGraphIso
    (fused (graph core4040) (root 5) 2 2) DegreeOneSmallSpectrum381.graph fusedMap4040=true := by decide +kernel
theorem certified4040 : Certified (graph core4040) (root 5) 2 2 :=
  of_native_maps core4040 DegreeOneSmallSpectrum816.graph DegreeOneSmallSpectrum381.graph
    sourceMap4040 fusedMap4040 sourceMap4040_checked fusedMap4040_checked
    DegreeTwoThreeFiniteComparisons.comparison4040
#print axioms sourceMap4040_checked
#print axioms fusedMap4040_checked
#print axioms certified4040
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
