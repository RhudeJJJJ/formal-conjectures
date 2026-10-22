/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0878 : Family 10 := level10.get ⟨625,by decide⟩
def sourceMap0878 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0878 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0878_checked : acceptsGraphIso
    (source (graph core0878) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2120.graph sourceMap0878=true := by decide +kernel
theorem fusedMap0878_checked : acceptsGraphIso
    (fused (graph core0878) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1182.graph fusedMap0878=true := by decide +kernel
theorem certified0878 : Certified (graph core0878) (root 10) 2 2 :=
  of_native_maps core0878 DegreeOneMiddleResidualSpectrum2120.graph DegreeOneMiddleResidualSpectrum1182.graph
    sourceMap0878 fusedMap0878 sourceMap0878_checked fusedMap0878_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0878
#print axioms sourceMap0878_checked
#print axioms fusedMap0878_checked
#print axioms certified0878
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
