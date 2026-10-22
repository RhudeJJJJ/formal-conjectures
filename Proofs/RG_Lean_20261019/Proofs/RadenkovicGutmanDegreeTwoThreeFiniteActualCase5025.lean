/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5025 : Family 10 := level10.get ⟨1700,by decide⟩
def sourceMap5025 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap5025 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5025_checked : acceptsGraphIso
    (source (graph core5025) (root 10) 2 2) DegreeTwoThreeSpectrum7626.graph sourceMap5025=true := by decide +kernel
theorem fusedMap5025_checked : acceptsGraphIso
    (fused (graph core5025) (root 10) 2 2) DegreeTwoThreeSpectrum6468.graph fusedMap5025=true := by decide +kernel
theorem certified5025 : Certified (graph core5025) (root 10) 2 2 :=
  of_native_maps core5025 DegreeTwoThreeSpectrum7626.graph DegreeTwoThreeSpectrum6468.graph
    sourceMap5025 fusedMap5025 sourceMap5025_checked fusedMap5025_checked
    DegreeTwoThreeFiniteComparisons.comparison5025
#print axioms sourceMap5025_checked
#print axioms fusedMap5025_checked
#print axioms certified5025
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
