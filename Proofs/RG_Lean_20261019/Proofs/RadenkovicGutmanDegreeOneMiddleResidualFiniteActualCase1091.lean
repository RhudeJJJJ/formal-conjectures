/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1091 : Family 10 := level10.get ⟨1138,by decide⟩
def sourceMap1091 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1091 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1091_checked : acceptsGraphIso
    (source (graph core1091) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2075.graph sourceMap1091=true := by decide +kernel
theorem fusedMap1091_checked : acceptsGraphIso
    (fused (graph core1091) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1629.graph fusedMap1091=true := by decide +kernel
theorem certified1091 : Certified (graph core1091) (root 10) 2 2 :=
  of_native_maps core1091 DegreeOneMiddleResidualSpectrum2075.graph DegreeOneMiddleResidualSpectrum1629.graph
    sourceMap1091 fusedMap1091 sourceMap1091_checked fusedMap1091_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1091
#print axioms sourceMap1091_checked
#print axioms fusedMap1091_checked
#print axioms certified1091
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
