/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0842 : Family 10 := level10.get ⟨564,by decide⟩
def sourceMap0842 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0842 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0842_checked : acceptsGraphIso
    (source (graph core0842) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2050.graph sourceMap0842=true := by decide +kernel
theorem fusedMap0842_checked : acceptsGraphIso
    (fused (graph core0842) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1126.graph fusedMap0842=true := by decide +kernel
theorem certified0842 : Certified (graph core0842) (root 10) 2 2 :=
  of_native_maps core0842 DegreeOneMiddleResidualSpectrum2050.graph DegreeOneMiddleResidualSpectrum1126.graph
    sourceMap0842 fusedMap0842 sourceMap0842_checked fusedMap0842_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0842
#print axioms sourceMap0842_checked
#print axioms fusedMap0842_checked
#print axioms certified0842
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
