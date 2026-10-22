/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1111 : Family 10 := level10.get ⟨1196,by decide⟩
def sourceMap1111 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1111 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1111_checked : acceptsGraphIso
    (source (graph core1111) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2119.graph sourceMap1111=true := by decide +kernel
theorem fusedMap1111_checked : acceptsGraphIso
    (fused (graph core1111) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1668.graph fusedMap1111=true := by decide +kernel
theorem certified1111 : Certified (graph core1111) (root 10) 2 2 :=
  of_native_maps core1111 DegreeOneMiddleResidualSpectrum2119.graph DegreeOneMiddleResidualSpectrum1668.graph
    sourceMap1111 fusedMap1111 sourceMap1111_checked fusedMap1111_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1111
#print axioms sourceMap1111_checked
#print axioms fusedMap1111_checked
#print axioms certified1111
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
