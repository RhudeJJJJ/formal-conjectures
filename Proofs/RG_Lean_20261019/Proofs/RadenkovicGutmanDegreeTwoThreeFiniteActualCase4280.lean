/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4280 : Family 9 := level9.get ⟨301,by decide⟩
def sourceMap4280 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4280 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4280_checked : acceptsGraphIso
    (source (graph core4280) (root 9) 2 2) DegreeTwoThreeSpectrum4899.graph sourceMap4280=true := by decide +kernel
theorem fusedMap4280_checked : acceptsGraphIso
    (fused (graph core4280) (root 9) 2 2) DegreeTwoThreeSpectrum4133.graph fusedMap4280=true := by decide +kernel
theorem certified4280 : Certified (graph core4280) (root 9) 2 2 :=
  of_native_maps core4280 DegreeTwoThreeSpectrum4899.graph DegreeTwoThreeSpectrum4133.graph
    sourceMap4280 fusedMap4280 sourceMap4280_checked fusedMap4280_checked
    DegreeTwoThreeFiniteComparisons.comparison4280
#print axioms sourceMap4280_checked
#print axioms fusedMap4280_checked
#print axioms certified4280
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
