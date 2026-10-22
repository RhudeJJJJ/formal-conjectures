/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0194 : Family 4 := level4.get ⟨0,by decide⟩
def sourceMap0194 : (Vertices 4 ⊕ Fin 5 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,11,12,13,14,1,2,3,4,5,6,7,8,9,10] (sourceLabel 4 4 4 v)
def fusedMap0194 : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13,14] (fusedLabel 4 4 4 v)
theorem sourceMap0194_checked : acceptsGraphIso
    (source (graph core0194) (root 4) 4 4) DegreeTwoThreeSpectrum2993.graph sourceMap0194=true := by decide +kernel
theorem fusedMap0194_checked : acceptsGraphIso
    (fused (graph core0194) (root 4) 4 4) DegreeOneMiddleResidualSpectrum111.graph fusedMap0194=true := by decide +kernel
theorem certified0194 : Certified (graph core0194) (root 4) 4 4 :=
  of_native_maps core0194 DegreeTwoThreeSpectrum2993.graph DegreeOneMiddleResidualSpectrum111.graph
    sourceMap0194 fusedMap0194 sourceMap0194_checked fusedMap0194_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0194
#print axioms sourceMap0194_checked
#print axioms fusedMap0194_checked
#print axioms certified0194
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
