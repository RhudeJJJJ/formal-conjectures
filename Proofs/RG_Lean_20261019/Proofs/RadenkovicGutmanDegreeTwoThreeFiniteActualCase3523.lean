/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3523 : Family 7 := level7.get ⟨68,by decide⟩
def sourceMap3523 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3523 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3523_checked : acceptsGraphIso
    (source (graph core3523) (root 7) 0 6) DegreeTwoThreeSpectrum4241.graph sourceMap3523=true := by decide +kernel
theorem fusedMap3523_checked : acceptsGraphIso
    (fused (graph core3523) (root 7) 0 6) DegreeTwoThreeSpectrum3903.graph fusedMap3523=true := by decide +kernel
theorem certified3523 : Certified (graph core3523) (root 7) 0 6 :=
  of_native_maps core3523 DegreeTwoThreeSpectrum4241.graph DegreeTwoThreeSpectrum3903.graph
    sourceMap3523 fusedMap3523 sourceMap3523_checked fusedMap3523_checked
    DegreeTwoThreeFiniteComparisons.comparison3523
#print axioms sourceMap3523_checked
#print axioms fusedMap3523_checked
#print axioms certified3523
def sourceMap3523swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,10] (sourceLabel 7 6 0 v)
def fusedMap3523swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3523swap_checked : acceptsGraphIso
    (source (graph core3523) (root 7) 6 0) DegreeTwoThreeSpectrum4241.graph sourceMap3523swap=true := by decide +kernel
theorem fusedMap3523swap_checked : acceptsGraphIso
    (fused (graph core3523) (root 7) 6 0) DegreeTwoThreeSpectrum3903.graph fusedMap3523swap=true := by decide +kernel
theorem certified3523swap : Certified (graph core3523) (root 7) 6 0 :=
  of_native_maps core3523 DegreeTwoThreeSpectrum4241.graph DegreeTwoThreeSpectrum3903.graph
    sourceMap3523swap fusedMap3523swap sourceMap3523swap_checked fusedMap3523swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3523
#print axioms sourceMap3523swap_checked
#print axioms fusedMap3523swap_checked
#print axioms certified3523swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
