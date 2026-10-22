/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4031 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap4031 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 10) → Fin 16 :=
  fun v => ![4,5,6,9,7,8,3,2,1,0,10,11,12,13,14,15] (sourceLabel 3 1 9 v)
def fusedMap4031 : (Vertices 3 ⊕ Fin 12) → Fin 16 :=
  fun v => ![5,6,7,8,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 3 1 9 v)
theorem sourceMap4031_checked : acceptsGraphIso
    (source (graph core4031) (root 3) 1 9) DegreeTwoThreeSpectrum3986.graph sourceMap4031=true := by decide +kernel
theorem fusedMap4031_checked : acceptsGraphIso
    (fused (graph core4031) (root 3) 1 9) DegreeTwoThreeSpectrum3869.graph fusedMap4031=true := by decide +kernel
theorem certified4031 : Certified (graph core4031) (root 3) 1 9 :=
  of_native_maps core4031 DegreeTwoThreeSpectrum3986.graph DegreeTwoThreeSpectrum3869.graph
    sourceMap4031 fusedMap4031 sourceMap4031_checked fusedMap4031_checked
    DegreeTwoThreeFiniteComparisons.comparison4031
#print axioms sourceMap4031_checked
#print axioms fusedMap4031_checked
#print axioms certified4031
def sourceMap4031swap : (Vertices 3 ⊕ Fin 10 ⊕ Fin 2) → Fin 16 :=
  fun v => ![4,5,6,9,3,2,1,0,10,11,12,13,14,15,7,8] (sourceLabel 3 9 1 v)
def fusedMap4031swap : (Vertices 3 ⊕ Fin 12) → Fin 16 :=
  fun v => ![5,6,7,8,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 3 9 1 v)
theorem sourceMap4031swap_checked : acceptsGraphIso
    (source (graph core4031) (root 3) 9 1) DegreeTwoThreeSpectrum3986.graph sourceMap4031swap=true := by decide +kernel
theorem fusedMap4031swap_checked : acceptsGraphIso
    (fused (graph core4031) (root 3) 9 1) DegreeTwoThreeSpectrum3869.graph fusedMap4031swap=true := by decide +kernel
theorem certified4031swap : Certified (graph core4031) (root 3) 9 1 :=
  of_native_maps core4031 DegreeTwoThreeSpectrum3986.graph DegreeTwoThreeSpectrum3869.graph
    sourceMap4031swap fusedMap4031swap sourceMap4031swap_checked fusedMap4031swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4031
#print axioms sourceMap4031swap_checked
#print axioms fusedMap4031swap_checked
#print axioms certified4031swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
