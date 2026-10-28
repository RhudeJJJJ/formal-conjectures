/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5033 : Family 10 := level10.get ⟨1714,by decide⟩
def sourceMap5033 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap5033 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5033_checked : acceptsGraphIso
    (source (graph core5033) (root 10) 2 2) DegreeTwoThreeSpectrum7634.graph sourceMap5033=true := by decide +kernel
theorem fusedMap5033_checked : acceptsGraphIso
    (fused (graph core5033) (root 10) 2 2) DegreeTwoThreeSpectrum6493.graph fusedMap5033=true := by decide +kernel
theorem certified5033 : Certified (graph core5033) (root 10) 2 2 :=
  of_native_maps core5033 DegreeTwoThreeSpectrum7634.graph DegreeTwoThreeSpectrum6493.graph
    sourceMap5033 fusedMap5033 sourceMap5033_checked fusedMap5033_checked
    DegreeTwoThreeFiniteComparisons.comparison5033
#print axioms sourceMap5033_checked
#print axioms fusedMap5033_checked
#print axioms certified5033
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
