/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5330 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap5330 : (Vertices 5 ⊕ Fin 4 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,9,5,6,7,8,10,11,12,13,14] (sourceLabel 5 3 4 v)
def fusedMap5330 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13,14] (fusedLabel 5 3 4 v)
theorem sourceMap5330_checked : acceptsGraphIso
    (source (graph core5330) (root 5) 3 4) DegreeTwoThreeSpectrum2941.graph sourceMap5330=true := by decide +kernel
theorem fusedMap5330_checked : acceptsGraphIso
    (fused (graph core5330) (root 5) 3 4) DegreeTwoThreeSpectrum2312.graph fusedMap5330=true := by decide +kernel
theorem certified5330 : Certified (graph core5330) (root 5) 3 4 :=
  of_native_maps core5330 DegreeTwoThreeSpectrum2941.graph DegreeTwoThreeSpectrum2312.graph
    sourceMap5330 fusedMap5330 sourceMap5330_checked fusedMap5330_checked
    DegreeTwoThreeFiniteComparisons.comparison5330
#print axioms sourceMap5330_checked
#print axioms fusedMap5330_checked
#print axioms certified5330
def sourceMap5330swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,14,5,6,7,8] (sourceLabel 5 4 3 v)
def fusedMap5330swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13,14] (fusedLabel 5 4 3 v)
theorem sourceMap5330swap_checked : acceptsGraphIso
    (source (graph core5330) (root 5) 4 3) DegreeTwoThreeSpectrum2941.graph sourceMap5330swap=true := by decide +kernel
theorem fusedMap5330swap_checked : acceptsGraphIso
    (fused (graph core5330) (root 5) 4 3) DegreeTwoThreeSpectrum2312.graph fusedMap5330swap=true := by decide +kernel
theorem certified5330swap : Certified (graph core5330) (root 5) 4 3 :=
  of_native_maps core5330 DegreeTwoThreeSpectrum2941.graph DegreeTwoThreeSpectrum2312.graph
    sourceMap5330swap fusedMap5330swap sourceMap5330swap_checked fusedMap5330swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5330
#print axioms sourceMap5330swap_checked
#print axioms fusedMap5330swap_checked
#print axioms certified5330swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
