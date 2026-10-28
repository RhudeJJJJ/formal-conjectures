/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5011 : Family 10 := level10.get ⟨1647,by decide⟩
def sourceMap5011 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap5011 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5011_checked : acceptsGraphIso
    (source (graph core5011) (root 10) 2 2) DegreeTwoThreeSpectrum7612.graph sourceMap5011=true := by decide +kernel
theorem fusedMap5011_checked : acceptsGraphIso
    (fused (graph core5011) (root 10) 2 2) DegreeTwoThreeSpectrum6237.graph fusedMap5011=true := by decide +kernel
theorem certified5011 : Certified (graph core5011) (root 10) 2 2 :=
  of_native_maps core5011 DegreeTwoThreeSpectrum7612.graph DegreeTwoThreeSpectrum6237.graph
    sourceMap5011 fusedMap5011 sourceMap5011_checked fusedMap5011_checked
    DegreeTwoThreeFiniteComparisons.comparison5011
#print axioms sourceMap5011_checked
#print axioms fusedMap5011_checked
#print axioms certified5011
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
