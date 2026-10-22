/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3017 : Family 10 := level10.get ⟨1603,by decide⟩
def sourceMap3017 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3017 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3017_checked : acceptsGraphIso
    (source (graph core3017) (root 10) 0 4) DegreeTwoThreeSpectrum7146.graph sourceMap3017=true := by decide +kernel
theorem fusedMap3017_checked : acceptsGraphIso
    (fused (graph core3017) (root 10) 0 4) DegreeTwoThreeSpectrum6119.graph fusedMap3017=true := by decide +kernel
theorem certified3017 : Certified (graph core3017) (root 10) 0 4 :=
  of_native_maps core3017 DegreeTwoThreeSpectrum7146.graph DegreeTwoThreeSpectrum6119.graph
    sourceMap3017 fusedMap3017 sourceMap3017_checked fusedMap3017_checked
    DegreeTwoThreeFiniteComparisons.comparison3017
#print axioms sourceMap3017_checked
#print axioms fusedMap3017_checked
#print axioms certified3017
def sourceMap3017swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3017swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3017swap_checked : acceptsGraphIso
    (source (graph core3017) (root 10) 4 0) DegreeTwoThreeSpectrum7146.graph sourceMap3017swap=true := by decide +kernel
theorem fusedMap3017swap_checked : acceptsGraphIso
    (fused (graph core3017) (root 10) 4 0) DegreeTwoThreeSpectrum6119.graph fusedMap3017swap=true := by decide +kernel
theorem certified3017swap : Certified (graph core3017) (root 10) 4 0 :=
  of_native_maps core3017 DegreeTwoThreeSpectrum7146.graph DegreeTwoThreeSpectrum6119.graph
    sourceMap3017swap fusedMap3017swap sourceMap3017swap_checked fusedMap3017swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3017
#print axioms sourceMap3017swap_checked
#print axioms fusedMap3017swap_checked
#print axioms certified3017swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
