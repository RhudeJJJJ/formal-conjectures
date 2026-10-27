/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4022 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap4022 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (sourceLabel 5 1 7 v)
def fusedMap4022 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 1 7 v)
theorem sourceMap4022_checked : acceptsGraphIso
    (source (graph core4022) (root 5) 1 7) DegreeTwoThreeSpectrum4068.graph sourceMap4022=true := by decide +kernel
theorem fusedMap4022_checked : acceptsGraphIso
    (fused (graph core4022) (root 5) 1 7) DegreeTwoThreeSpectrum3870.graph fusedMap4022=true := by decide +kernel
theorem certified4022 : Certified (graph core4022) (root 5) 1 7 :=
  of_native_maps core4022 DegreeTwoThreeSpectrum4068.graph DegreeTwoThreeSpectrum3870.graph
    sourceMap4022 fusedMap4022 sourceMap4022_checked fusedMap4022_checked
    DegreeTwoThreeFiniteComparisons.comparison4022
#print axioms sourceMap4022_checked
#print axioms fusedMap4022_checked
#print axioms certified4022
def sourceMap4022swap : (Vertices 5 ⊕ Fin 8 ⊕ Fin 2) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,1,0,10,11,12,13,14,15,8,9] (sourceLabel 5 7 1 v)
def fusedMap4022swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 7 1 v)
theorem sourceMap4022swap_checked : acceptsGraphIso
    (source (graph core4022) (root 5) 7 1) DegreeTwoThreeSpectrum4068.graph sourceMap4022swap=true := by decide +kernel
theorem fusedMap4022swap_checked : acceptsGraphIso
    (fused (graph core4022) (root 5) 7 1) DegreeTwoThreeSpectrum3870.graph fusedMap4022swap=true := by decide +kernel
theorem certified4022swap : Certified (graph core4022) (root 5) 7 1 :=
  of_native_maps core4022 DegreeTwoThreeSpectrum4068.graph DegreeTwoThreeSpectrum3870.graph
    sourceMap4022swap fusedMap4022swap sourceMap4022swap_checked fusedMap4022swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4022
#print axioms sourceMap4022swap_checked
#print axioms fusedMap4022swap_checked
#print axioms certified4022swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
