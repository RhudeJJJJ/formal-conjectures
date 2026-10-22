/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4004 : Family 6 := level6.get ⟨24,by decide⟩
def sourceMap4004 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,10,8,9,1,0,11,12,13,14,15] (sourceLabel 6 1 6 v)
def fusedMap4004 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 1 6 v)
theorem sourceMap4004_checked : acceptsGraphIso
    (source (graph core4004) (root 6) 1 6) DegreeTwoThreeSpectrum4311.graph sourceMap4004=true := by decide +kernel
theorem fusedMap4004_checked : acceptsGraphIso
    (fused (graph core4004) (root 6) 1 6) DegreeTwoThreeSpectrum3931.graph fusedMap4004=true := by decide +kernel
theorem certified4004 : Certified (graph core4004) (root 6) 1 6 :=
  of_native_maps core4004 DegreeTwoThreeSpectrum4311.graph DegreeTwoThreeSpectrum3931.graph
    sourceMap4004 fusedMap4004 sourceMap4004_checked fusedMap4004_checked
    DegreeTwoThreeFiniteComparisons.comparison4004
#print axioms sourceMap4004_checked
#print axioms fusedMap4004_checked
#print axioms certified4004
def sourceMap4004swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 2) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,10,1,0,11,12,13,14,15,8,9] (sourceLabel 6 6 1 v)
def fusedMap4004swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 6 1 v)
theorem sourceMap4004swap_checked : acceptsGraphIso
    (source (graph core4004) (root 6) 6 1) DegreeTwoThreeSpectrum4311.graph sourceMap4004swap=true := by decide +kernel
theorem fusedMap4004swap_checked : acceptsGraphIso
    (fused (graph core4004) (root 6) 6 1) DegreeTwoThreeSpectrum3931.graph fusedMap4004swap=true := by decide +kernel
theorem certified4004swap : Certified (graph core4004) (root 6) 6 1 :=
  of_native_maps core4004 DegreeTwoThreeSpectrum4311.graph DegreeTwoThreeSpectrum3931.graph
    sourceMap4004swap fusedMap4004swap sourceMap4004swap_checked fusedMap4004swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4004
#print axioms sourceMap4004swap_checked
#print axioms fusedMap4004swap_checked
#print axioms certified4004swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
