/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3075 : Family 10 := level10.get ⟨1812,by decide⟩
def sourceMap3075 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3075 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,12,1,0,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3075_checked : acceptsGraphIso
    (source (graph core3075) (root 10) 0 4) DegreeTwoThreeSpectrum7081.graph sourceMap3075=true := by decide +kernel
theorem fusedMap3075_checked : acceptsGraphIso
    (fused (graph core3075) (root 10) 0 4) DegreeTwoThreeSpectrum7082.graph fusedMap3075=true := by decide +kernel
theorem certified3075 : Certified (graph core3075) (root 10) 0 4 :=
  of_native_maps core3075 DegreeTwoThreeSpectrum7081.graph DegreeTwoThreeSpectrum7082.graph
    sourceMap3075 fusedMap3075 sourceMap3075_checked fusedMap3075_checked
    DegreeTwoThreeFiniteComparisons.comparison3075
#print axioms sourceMap3075_checked
#print axioms fusedMap3075_checked
#print axioms certified3075
def sourceMap3075swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3075swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,12,1,0,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3075swap_checked : acceptsGraphIso
    (source (graph core3075) (root 10) 4 0) DegreeTwoThreeSpectrum7081.graph sourceMap3075swap=true := by decide +kernel
theorem fusedMap3075swap_checked : acceptsGraphIso
    (fused (graph core3075) (root 10) 4 0) DegreeTwoThreeSpectrum7082.graph fusedMap3075swap=true := by decide +kernel
theorem certified3075swap : Certified (graph core3075) (root 10) 4 0 :=
  of_native_maps core3075 DegreeTwoThreeSpectrum7081.graph DegreeTwoThreeSpectrum7082.graph
    sourceMap3075swap fusedMap3075swap sourceMap3075swap_checked fusedMap3075swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3075
#print axioms sourceMap3075swap_checked
#print axioms fusedMap3075swap_checked
#print axioms certified3075swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
