/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4000 : Family 6 := level6.get ⟨13,by decide⟩
def sourceMap4000 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,9,7,8,0,10,11,12,13,14,15] (sourceLabel 6 1 6 v)
def fusedMap4000 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 1 6 v)
theorem sourceMap4000_checked : acceptsGraphIso
    (source (graph core4000) (root 6) 1 6) DegreeTwoThreeSpectrum4038.graph sourceMap4000=true := by decide +kernel
theorem fusedMap4000_checked : acceptsGraphIso
    (fused (graph core4000) (root 6) 1 6) DegreeTwoThreeSpectrum3865.graph fusedMap4000=true := by decide +kernel
theorem certified4000 : Certified (graph core4000) (root 6) 1 6 :=
  of_native_maps core4000 DegreeTwoThreeSpectrum4038.graph DegreeTwoThreeSpectrum3865.graph
    sourceMap4000 fusedMap4000 sourceMap4000_checked fusedMap4000_checked
    DegreeTwoThreeFiniteComparisons.comparison4000
#print axioms sourceMap4000_checked
#print axioms fusedMap4000_checked
#print axioms certified4000
def sourceMap4000swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,9,0,10,11,12,13,14,15,7,8] (sourceLabel 6 6 1 v)
def fusedMap4000swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 6 1 v)
theorem sourceMap4000swap_checked : acceptsGraphIso
    (source (graph core4000) (root 6) 6 1) DegreeTwoThreeSpectrum4038.graph sourceMap4000swap=true := by decide +kernel
theorem fusedMap4000swap_checked : acceptsGraphIso
    (fused (graph core4000) (root 6) 6 1) DegreeTwoThreeSpectrum3865.graph fusedMap4000swap=true := by decide +kernel
theorem certified4000swap : Certified (graph core4000) (root 6) 6 1 :=
  of_native_maps core4000 DegreeTwoThreeSpectrum4038.graph DegreeTwoThreeSpectrum3865.graph
    sourceMap4000swap fusedMap4000swap sourceMap4000swap_checked fusedMap4000swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4000
#print axioms sourceMap4000swap_checked
#print axioms fusedMap4000swap_checked
#print axioms certified4000swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
