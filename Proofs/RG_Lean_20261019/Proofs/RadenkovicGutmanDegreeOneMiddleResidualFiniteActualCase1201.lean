/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1201 : Family 10 := level10.get ⟨1736,by decide⟩
def sourceMap1201 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1201 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1201_checked : acceptsGraphIso
    (source (graph core1201) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2357.graph sourceMap1201=true := by decide +kernel
theorem fusedMap1201_checked : acceptsGraphIso
    (fused (graph core1201) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1749.graph fusedMap1201=true := by decide +kernel
theorem certified1201 : Certified (graph core1201) (root 10) 2 2 :=
  of_native_maps core1201 DegreeOneMiddleResidualSpectrum2357.graph DegreeOneMiddleResidualSpectrum1749.graph
    sourceMap1201 fusedMap1201 sourceMap1201_checked fusedMap1201_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1201
#print axioms sourceMap1201_checked
#print axioms fusedMap1201_checked
#print axioms certified1201
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
