/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0898 : Family 10 := level10.get ⟨666,by decide⟩
def sourceMap0898 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap0898 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0898_checked : acceptsGraphIso
    (source (graph core0898) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2141.graph sourceMap0898=true := by decide +kernel
theorem fusedMap0898_checked : acceptsGraphIso
    (fused (graph core0898) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1218.graph fusedMap0898=true := by decide +kernel
theorem certified0898 : Certified (graph core0898) (root 10) 2 2 :=
  of_native_maps core0898 DegreeOneMiddleResidualSpectrum2141.graph DegreeOneMiddleResidualSpectrum1218.graph
    sourceMap0898 fusedMap0898 sourceMap0898_checked fusedMap0898_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0898
#print axioms sourceMap0898_checked
#print axioms fusedMap0898_checked
#print axioms certified0898
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
