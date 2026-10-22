/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0085 : Family 8 := level8.get ⟨34,by decide⟩
def sourceMap0085 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0085 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0085_checked : acceptsGraphIso
    (source (graph core0085) (root 8) 2 2) DegreeOneMiddleResidualSpectrum266.graph sourceMap0085=true := by decide +kernel
theorem fusedMap0085_checked : acceptsGraphIso
    (fused (graph core0085) (root 8) 2 2) DegreeOneMiddleResidualSpectrum112.graph fusedMap0085=true := by decide +kernel
theorem certified0085 : Certified (graph core0085) (root 8) 2 2 :=
  of_native_maps core0085 DegreeOneMiddleResidualSpectrum266.graph DegreeOneMiddleResidualSpectrum112.graph
    sourceMap0085 fusedMap0085 sourceMap0085_checked fusedMap0085_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0085
#print axioms sourceMap0085_checked
#print axioms fusedMap0085_checked
#print axioms certified0085
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
