/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3621 : Family 8 := level8.get ⟨234,by decide⟩
def sourceMap3621 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3621 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3621_checked : acceptsGraphIso
    (source (graph core3621) (root 8) 0 6) DegreeTwoThreeSpectrum6509.graph sourceMap3621=true := by decide +kernel
theorem fusedMap3621_checked : acceptsGraphIso
    (fused (graph core3621) (root 8) 0 6) DegreeTwoThreeSpectrum5427.graph fusedMap3621=true := by decide +kernel
theorem certified3621 : Certified (graph core3621) (root 8) 0 6 :=
  of_native_maps core3621 DegreeTwoThreeSpectrum6509.graph DegreeTwoThreeSpectrum5427.graph
    sourceMap3621 fusedMap3621 sourceMap3621_checked fusedMap3621_checked
    DegreeTwoThreeFiniteComparisons.comparison3621
#print axioms sourceMap3621_checked
#print axioms fusedMap3621_checked
#print axioms certified3621
def sourceMap3621swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3621swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3621swap_checked : acceptsGraphIso
    (source (graph core3621) (root 8) 6 0) DegreeTwoThreeSpectrum6509.graph sourceMap3621swap=true := by decide +kernel
theorem fusedMap3621swap_checked : acceptsGraphIso
    (fused (graph core3621) (root 8) 6 0) DegreeTwoThreeSpectrum5427.graph fusedMap3621swap=true := by decide +kernel
theorem certified3621swap : Certified (graph core3621) (root 8) 6 0 :=
  of_native_maps core3621 DegreeTwoThreeSpectrum6509.graph DegreeTwoThreeSpectrum5427.graph
    sourceMap3621swap fusedMap3621swap sourceMap3621swap_checked fusedMap3621swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3621
#print axioms sourceMap3621swap_checked
#print axioms fusedMap3621swap_checked
#print axioms certified3621swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
