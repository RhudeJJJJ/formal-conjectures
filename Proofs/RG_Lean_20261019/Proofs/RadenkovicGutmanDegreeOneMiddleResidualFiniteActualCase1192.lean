/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1192 : Family 10 := level10.get ⟨1615,by decide⟩
def sourceMap1192 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1192 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1192_checked : acceptsGraphIso
    (source (graph core1192) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2348.graph sourceMap1192=true := by decide +kernel
theorem fusedMap1192_checked : acceptsGraphIso
    (fused (graph core1192) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1594.graph fusedMap1192=true := by decide +kernel
theorem certified1192 : Certified (graph core1192) (root 10) 2 2 :=
  of_native_maps core1192 DegreeOneMiddleResidualSpectrum2348.graph DegreeOneMiddleResidualSpectrum1594.graph
    sourceMap1192 fusedMap1192 sourceMap1192_checked fusedMap1192_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1192
#print axioms sourceMap1192_checked
#print axioms fusedMap1192_checked
#print axioms certified1192
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
