/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1027 : Family 10 := level10.get ⟨996,by decide⟩
def sourceMap1027 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1027 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1027_checked : acceptsGraphIso
    (source (graph core1027) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1958.graph sourceMap1027=true := by decide +kernel
theorem fusedMap1027_checked : acceptsGraphIso
    (fused (graph core1027) (root 10) 2 2) DegreeTwoThreeSpectrum5965.graph fusedMap1027=true := by decide +kernel
theorem certified1027 : Certified (graph core1027) (root 10) 2 2 :=
  of_native_maps core1027 DegreeOneMiddleResidualSpectrum1958.graph DegreeTwoThreeSpectrum5965.graph
    sourceMap1027 fusedMap1027 sourceMap1027_checked fusedMap1027_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1027
#print axioms sourceMap1027_checked
#print axioms fusedMap1027_checked
#print axioms certified1027
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
