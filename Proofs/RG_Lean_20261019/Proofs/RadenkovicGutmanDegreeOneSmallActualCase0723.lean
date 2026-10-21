/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0723 : Family 7 := level7.get ⟨86,by decide⟩
def sourceMap0723 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,4,5,6,7,8,9,2,3] (sourceLabel 7 0 0 v)
def fusedMap0723 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0723_checked : acceptsGraphIso
    (source (graph core0723) (root 7) 0 0) SmallGeFourSpectrum032.graph sourceMap0723=true := by decide +kernel
theorem fusedMap0723_checked : acceptsGraphIso
    (fused (graph core0723) (root 7) 0 0) SmallGeFourSpectrum020.graph fusedMap0723=true := by decide +kernel
theorem certified0723 : Certified (graph core0723) (root 7) 0 0 :=
  of_native_maps core0723 SmallGeFourSpectrum032.graph SmallGeFourSpectrum020.graph
    sourceMap0723 fusedMap0723 sourceMap0723_checked fusedMap0723_checked
    DegreeOneSmallComparisons.comparison0723
#print axioms sourceMap0723_checked
#print axioms fusedMap0723_checked
#print axioms certified0723
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
