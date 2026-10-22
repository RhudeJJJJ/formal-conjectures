/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0968 : Family 10 := level10.get ⟨809,by decide⟩
def sourceMap0968 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap0968 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0968_checked : acceptsGraphIso
    (source (graph core0968) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2256.graph sourceMap0968=true := by decide +kernel
theorem fusedMap0968_checked : acceptsGraphIso
    (fused (graph core0968) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1346.graph fusedMap0968=true := by decide +kernel
theorem certified0968 : Certified (graph core0968) (root 10) 2 2 :=
  of_native_maps core0968 DegreeOneMiddleResidualSpectrum2256.graph DegreeOneMiddleResidualSpectrum1346.graph
    sourceMap0968 fusedMap0968 sourceMap0968_checked fusedMap0968_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0968
#print axioms sourceMap0968_checked
#print axioms fusedMap0968_checked
#print axioms certified0968
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
