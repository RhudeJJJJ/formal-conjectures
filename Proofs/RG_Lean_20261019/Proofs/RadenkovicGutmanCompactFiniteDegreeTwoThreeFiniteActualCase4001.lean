/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4001 : Family 6 := level6.get ⟨16,by decide⟩
def sourceMap4001 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,9,7,8,0,10,11,12,13,14,15] (sourceLabel 6 1 6 v)
def fusedMap4001 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 1 6 v)
theorem sourceMap4001_checked : acceptsGraphIso
    (source (graph core4001) (root 6) 1 6) DegreeTwoThreeSpectrum4094.graph sourceMap4001=true := by decide +kernel
theorem fusedMap4001_checked : acceptsGraphIso
    (fused (graph core4001) (root 6) 1 6) DegreeTwoThreeSpectrum3872.graph fusedMap4001=true := by decide +kernel
theorem certified4001 : Certified (graph core4001) (root 6) 1 6 :=
  of_native_maps core4001 DegreeTwoThreeSpectrum4094.graph DegreeTwoThreeSpectrum3872.graph
    sourceMap4001 fusedMap4001 sourceMap4001_checked fusedMap4001_checked
    DegreeTwoThreeFiniteComparisons.comparison4001
#print axioms sourceMap4001_checked
#print axioms fusedMap4001_checked
#print axioms certified4001
def sourceMap4001swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,9,0,10,11,12,13,14,15,7,8] (sourceLabel 6 6 1 v)
def fusedMap4001swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 6 1 v)
theorem sourceMap4001swap_checked : acceptsGraphIso
    (source (graph core4001) (root 6) 6 1) DegreeTwoThreeSpectrum4094.graph sourceMap4001swap=true := by decide +kernel
theorem fusedMap4001swap_checked : acceptsGraphIso
    (fused (graph core4001) (root 6) 6 1) DegreeTwoThreeSpectrum3872.graph fusedMap4001swap=true := by decide +kernel
theorem certified4001swap : Certified (graph core4001) (root 6) 6 1 :=
  of_native_maps core4001 DegreeTwoThreeSpectrum4094.graph DegreeTwoThreeSpectrum3872.graph
    sourceMap4001swap fusedMap4001swap sourceMap4001swap_checked fusedMap4001swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4001
#print axioms sourceMap4001swap_checked
#print axioms fusedMap4001swap_checked
#print axioms certified4001swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
