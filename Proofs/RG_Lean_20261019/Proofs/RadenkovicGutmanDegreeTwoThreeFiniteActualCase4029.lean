/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4029 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap4029 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (sourceLabel 4 1 8 v)
def fusedMap4029 : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 1 8 v)
theorem sourceMap4029_checked : acceptsGraphIso
    (source (graph core4029) (root 4) 1 8) DegreeTwoThreeSpectrum3982.graph sourceMap4029=true := by decide +kernel
theorem fusedMap4029_checked : acceptsGraphIso
    (fused (graph core4029) (root 4) 1 8) DegreeTwoThreeSpectrum3862.graph fusedMap4029=true := by decide +kernel
theorem certified4029 : Certified (graph core4029) (root 4) 1 8 :=
  of_native_maps core4029 DegreeTwoThreeSpectrum3982.graph DegreeTwoThreeSpectrum3862.graph
    sourceMap4029 fusedMap4029 sourceMap4029_checked fusedMap4029_checked
    DegreeTwoThreeFiniteComparisons.comparison4029
#print axioms sourceMap4029_checked
#print axioms fusedMap4029_checked
#print axioms certified4029
def sourceMap4029swap : (Vertices 4 ⊕ Fin 9 ⊕ Fin 2) → Fin 16 :=
  fun v => ![3,4,5,6,7,2,1,0,10,11,12,13,14,15,8,9] (sourceLabel 4 8 1 v)
def fusedMap4029swap : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 8 1 v)
theorem sourceMap4029swap_checked : acceptsGraphIso
    (source (graph core4029) (root 4) 8 1) DegreeTwoThreeSpectrum3982.graph sourceMap4029swap=true := by decide +kernel
theorem fusedMap4029swap_checked : acceptsGraphIso
    (fused (graph core4029) (root 4) 8 1) DegreeTwoThreeSpectrum3862.graph fusedMap4029swap=true := by decide +kernel
theorem certified4029swap : Certified (graph core4029) (root 4) 8 1 :=
  of_native_maps core4029 DegreeTwoThreeSpectrum3982.graph DegreeTwoThreeSpectrum3862.graph
    sourceMap4029swap fusedMap4029swap sourceMap4029swap_checked fusedMap4029swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4029
#print axioms sourceMap4029swap_checked
#print axioms fusedMap4029swap_checked
#print axioms certified4029swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
