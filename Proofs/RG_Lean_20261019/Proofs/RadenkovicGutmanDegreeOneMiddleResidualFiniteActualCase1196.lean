/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1196 : Family 10 := level10.get ⟨1630,by decide⟩
def sourceMap1196 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1196 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1196_checked : acceptsGraphIso
    (source (graph core1196) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2352.graph sourceMap1196=true := by decide +kernel
theorem fusedMap1196_checked : acceptsGraphIso
    (fused (graph core1196) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1606.graph fusedMap1196=true := by decide +kernel
theorem certified1196 : Certified (graph core1196) (root 10) 2 2 :=
  of_native_maps core1196 DegreeOneMiddleResidualSpectrum2352.graph DegreeOneMiddleResidualSpectrum1606.graph
    sourceMap1196 fusedMap1196 sourceMap1196_checked fusedMap1196_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1196
#print axioms sourceMap1196_checked
#print axioms fusedMap1196_checked
#print axioms certified1196
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
