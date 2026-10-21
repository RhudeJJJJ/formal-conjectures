/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0984 : Family 8 := level8.get ⟨95,by decide⟩
def sourceMap0984 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap0984 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0984_checked : acceptsGraphIso
    (source (graph core0984) (root 8) 0 1) SmallGeFourSpectrum127.graph sourceMap0984=true := by decide +kernel
theorem fusedMap0984_checked : acceptsGraphIso
    (fused (graph core0984) (root 8) 0 1) SmallGeFourSpectrum093.graph fusedMap0984=true := by decide +kernel
theorem certified0984 : Certified (graph core0984) (root 8) 0 1 :=
  of_native_maps core0984 SmallGeFourSpectrum127.graph SmallGeFourSpectrum093.graph
    sourceMap0984 fusedMap0984 sourceMap0984_checked fusedMap0984_checked
    DegreeOneSmallComparisons.comparison0984
#print axioms sourceMap0984_checked
#print axioms fusedMap0984_checked
#print axioms certified0984
def sourceMap0984swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap0984swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0984swap_checked : acceptsGraphIso
    (source (graph core0984) (root 8) 1 0) SmallGeFourSpectrum127.graph sourceMap0984swap=true := by decide +kernel
theorem fusedMap0984swap_checked : acceptsGraphIso
    (fused (graph core0984) (root 8) 1 0) SmallGeFourSpectrum093.graph fusedMap0984swap=true := by decide +kernel
theorem certified0984swap : Certified (graph core0984) (root 8) 1 0 :=
  of_native_maps core0984 SmallGeFourSpectrum127.graph SmallGeFourSpectrum093.graph
    sourceMap0984swap fusedMap0984swap sourceMap0984swap_checked fusedMap0984swap_checked
    DegreeOneSmallComparisons.comparison0984
#print axioms sourceMap0984swap_checked
#print axioms fusedMap0984swap_checked
#print axioms certified0984swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
