/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0181 : Family 6 := level6.get ⟨8,by decide⟩
def sourceMap0181 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap0181 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap0181_checked : acceptsGraphIso
    (source (graph core0181) (root 6) 2 4) DegreeOneMiddleResidualSpectrum202.graph sourceMap0181=true := by decide +kernel
theorem fusedMap0181_checked : acceptsGraphIso
    (fused (graph core0181) (root 6) 2 4) DegreeTwoThreeSpectrum2333.graph fusedMap0181=true := by decide +kernel
theorem certified0181 : Certified (graph core0181) (root 6) 2 4 :=
  of_native_maps core0181 DegreeOneMiddleResidualSpectrum202.graph DegreeTwoThreeSpectrum2333.graph
    sourceMap0181 fusedMap0181 sourceMap0181_checked fusedMap0181_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0181
#print axioms sourceMap0181_checked
#print axioms fusedMap0181_checked
#print axioms certified0181
def sourceMap0181swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,7,8,9] (sourceLabel 6 4 2 v)
def fusedMap0181swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap0181swap_checked : acceptsGraphIso
    (source (graph core0181) (root 6) 4 2) DegreeOneMiddleResidualSpectrum202.graph sourceMap0181swap=true := by decide +kernel
theorem fusedMap0181swap_checked : acceptsGraphIso
    (fused (graph core0181) (root 6) 4 2) DegreeTwoThreeSpectrum2333.graph fusedMap0181swap=true := by decide +kernel
theorem certified0181swap : Certified (graph core0181) (root 6) 4 2 :=
  of_native_maps core0181 DegreeOneMiddleResidualSpectrum202.graph DegreeTwoThreeSpectrum2333.graph
    sourceMap0181swap fusedMap0181swap sourceMap0181swap_checked fusedMap0181swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0181
#print axioms sourceMap0181swap_checked
#print axioms fusedMap0181swap_checked
#print axioms certified0181swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
