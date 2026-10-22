/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1199 : Family 10 := level10.get ⟨1701,by decide⟩
def sourceMap1199 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1199 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1199_checked : acceptsGraphIso
    (source (graph core1199) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2355.graph sourceMap1199=true := by decide +kernel
theorem fusedMap1199_checked : acceptsGraphIso
    (fused (graph core1199) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1709.graph fusedMap1199=true := by decide +kernel
theorem certified1199 : Certified (graph core1199) (root 10) 2 2 :=
  of_native_maps core1199 DegreeOneMiddleResidualSpectrum2355.graph DegreeOneMiddleResidualSpectrum1709.graph
    sourceMap1199 fusedMap1199 sourceMap1199_checked fusedMap1199_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1199
#print axioms sourceMap1199_checked
#print axioms fusedMap1199_checked
#print axioms certified1199
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
