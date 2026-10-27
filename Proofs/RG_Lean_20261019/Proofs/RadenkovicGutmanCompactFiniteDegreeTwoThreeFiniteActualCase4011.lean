/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4011 : Family 6 := level6.get ⟨38,by decide⟩
def sourceMap4011 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,10,8,9,1,0,11,12,13,14,15] (sourceLabel 6 1 6 v)
def fusedMap4011 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 1 6 v)
theorem sourceMap4011_checked : acceptsGraphIso
    (source (graph core4011) (root 6) 1 6) DegreeTwoThreeSpectrum4183.graph sourceMap4011=true := by decide +kernel
theorem fusedMap4011_checked : acceptsGraphIso
    (fused (graph core4011) (root 6) 1 6) DegreeTwoThreeSpectrum3893.graph fusedMap4011=true := by decide +kernel
theorem certified4011 : Certified (graph core4011) (root 6) 1 6 :=
  of_native_maps core4011 DegreeTwoThreeSpectrum4183.graph DegreeTwoThreeSpectrum3893.graph
    sourceMap4011 fusedMap4011 sourceMap4011_checked fusedMap4011_checked
    DegreeTwoThreeFiniteComparisons.comparison4011
#print axioms sourceMap4011_checked
#print axioms fusedMap4011_checked
#print axioms certified4011
def sourceMap4011swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 2) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,10,1,0,11,12,13,14,15,8,9] (sourceLabel 6 6 1 v)
def fusedMap4011swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 6 1 v)
theorem sourceMap4011swap_checked : acceptsGraphIso
    (source (graph core4011) (root 6) 6 1) DegreeTwoThreeSpectrum4183.graph sourceMap4011swap=true := by decide +kernel
theorem fusedMap4011swap_checked : acceptsGraphIso
    (fused (graph core4011) (root 6) 6 1) DegreeTwoThreeSpectrum3893.graph fusedMap4011swap=true := by decide +kernel
theorem certified4011swap : Certified (graph core4011) (root 6) 6 1 :=
  of_native_maps core4011 DegreeTwoThreeSpectrum4183.graph DegreeTwoThreeSpectrum3893.graph
    sourceMap4011swap fusedMap4011swap sourceMap4011swap_checked fusedMap4011swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4011
#print axioms sourceMap4011swap_checked
#print axioms fusedMap4011swap_checked
#print axioms certified4011swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
