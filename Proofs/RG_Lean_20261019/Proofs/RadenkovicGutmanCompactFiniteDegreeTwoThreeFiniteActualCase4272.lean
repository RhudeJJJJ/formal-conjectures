/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4272 : Family 9 := level9.get ⟨280,by decide⟩
def sourceMap4272 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4272 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4272_checked : acceptsGraphIso
    (source (graph core4272) (root 9) 2 2) DegreeTwoThreeSpectrum4895.graph sourceMap4272=true := by decide +kernel
theorem fusedMap4272_checked : acceptsGraphIso
    (fused (graph core4272) (root 9) 2 2) DegreeTwoThreeSpectrum4097.graph fusedMap4272=true := by decide +kernel
theorem certified4272 : Certified (graph core4272) (root 9) 2 2 :=
  of_native_maps core4272 DegreeTwoThreeSpectrum4895.graph DegreeTwoThreeSpectrum4097.graph
    sourceMap4272 fusedMap4272 sourceMap4272_checked fusedMap4272_checked
    DegreeTwoThreeFiniteComparisons.comparison4272
#print axioms sourceMap4272_checked
#print axioms fusedMap4272_checked
#print axioms certified4272
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
