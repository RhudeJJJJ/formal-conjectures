/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0318 : Family 6 := level6.get ⟨6,by decide⟩
def sourceMap0318 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 6 1 2 v)
def fusedMap0318 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap0318_checked : acceptsGraphIso
    (source (graph core0318) (root 6) 1 2) DegreeOneSmallSpectrum424.graph sourceMap0318=true := by decide +kernel
theorem fusedMap0318_checked : acceptsGraphIso
    (fused (graph core0318) (root 6) 1 2) DegreeOneSmallSpectrum370.graph fusedMap0318=true := by decide +kernel
theorem certified0318 : Certified (graph core0318) (root 6) 1 2 :=
  of_native_maps core0318 DegreeOneSmallSpectrum424.graph DegreeOneSmallSpectrum370.graph
    sourceMap0318 fusedMap0318 sourceMap0318_checked fusedMap0318_checked
    DegreeOneSmallComparisons.comparison0318
#print axioms sourceMap0318_checked
#print axioms fusedMap0318_checked
#print axioms certified0318
def sourceMap0318swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 6 2 1 v)
def fusedMap0318swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap0318swap_checked : acceptsGraphIso
    (source (graph core0318) (root 6) 2 1) DegreeOneSmallSpectrum424.graph sourceMap0318swap=true := by decide +kernel
theorem fusedMap0318swap_checked : acceptsGraphIso
    (fused (graph core0318) (root 6) 2 1) DegreeOneSmallSpectrum370.graph fusedMap0318swap=true := by decide +kernel
theorem certified0318swap : Certified (graph core0318) (root 6) 2 1 :=
  of_native_maps core0318 DegreeOneSmallSpectrum424.graph DegreeOneSmallSpectrum370.graph
    sourceMap0318swap fusedMap0318swap sourceMap0318swap_checked fusedMap0318swap_checked
    DegreeOneSmallComparisons.comparison0318
#print axioms sourceMap0318swap_checked
#print axioms fusedMap0318swap_checked
#print axioms certified0318swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
