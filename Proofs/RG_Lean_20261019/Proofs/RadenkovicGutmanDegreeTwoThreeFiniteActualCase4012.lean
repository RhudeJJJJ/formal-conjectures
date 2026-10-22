/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4012 : Family 6 := level6.get ⟨39,by decide⟩
def sourceMap4012 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 6 1 6 v)
def fusedMap4012 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 1 6 v)
theorem sourceMap4012_checked : acceptsGraphIso
    (source (graph core4012) (root 6) 1 6) DegreeTwoThreeSpectrum4208.graph sourceMap4012=true := by decide +kernel
theorem fusedMap4012_checked : acceptsGraphIso
    (fused (graph core4012) (root 6) 1 6) DegreeTwoThreeSpectrum3897.graph fusedMap4012=true := by decide +kernel
theorem certified4012 : Certified (graph core4012) (root 6) 1 6 :=
  of_native_maps core4012 DegreeTwoThreeSpectrum4208.graph DegreeTwoThreeSpectrum3897.graph
    sourceMap4012 fusedMap4012 sourceMap4012_checked fusedMap4012_checked
    DegreeTwoThreeFiniteComparisons.comparison4012
#print axioms sourceMap4012_checked
#print axioms fusedMap4012_checked
#print axioms certified4012
def sourceMap4012swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 2) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,11,12,13,14,15,9,10] (sourceLabel 6 6 1 v)
def fusedMap4012swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 6 1 v)
theorem sourceMap4012swap_checked : acceptsGraphIso
    (source (graph core4012) (root 6) 6 1) DegreeTwoThreeSpectrum4208.graph sourceMap4012swap=true := by decide +kernel
theorem fusedMap4012swap_checked : acceptsGraphIso
    (fused (graph core4012) (root 6) 6 1) DegreeTwoThreeSpectrum3897.graph fusedMap4012swap=true := by decide +kernel
theorem certified4012swap : Certified (graph core4012) (root 6) 6 1 :=
  of_native_maps core4012 DegreeTwoThreeSpectrum4208.graph DegreeTwoThreeSpectrum3897.graph
    sourceMap4012swap fusedMap4012swap sourceMap4012swap_checked fusedMap4012swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4012
#print axioms sourceMap4012swap_checked
#print axioms fusedMap4012swap_checked
#print axioms certified4012swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
