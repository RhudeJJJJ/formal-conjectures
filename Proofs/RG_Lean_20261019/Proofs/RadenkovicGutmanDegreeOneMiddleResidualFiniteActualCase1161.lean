/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1161 : Family 10 := level10.get ⟨1409,by decide⟩
def sourceMap1161 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1161 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1161_checked : acceptsGraphIso
    (source (graph core1161) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2262.graph sourceMap1161=true := by decide +kernel
theorem fusedMap1161_checked : acceptsGraphIso
    (fused (graph core1161) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1835.graph fusedMap1161=true := by decide +kernel
theorem certified1161 : Certified (graph core1161) (root 10) 2 2 :=
  of_native_maps core1161 DegreeOneMiddleResidualSpectrum2262.graph DegreeOneMiddleResidualSpectrum1835.graph
    sourceMap1161 fusedMap1161 sourceMap1161_checked fusedMap1161_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1161
#print axioms sourceMap1161_checked
#print axioms fusedMap1161_checked
#print axioms certified1161
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
