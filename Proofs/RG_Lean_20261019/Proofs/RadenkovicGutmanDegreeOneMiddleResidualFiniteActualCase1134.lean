/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1134 : Family 10 := level10.get ⟨1298,by decide⟩
def sourceMap1134 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1134 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1134_checked : acceptsGraphIso
    (source (graph core1134) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2186.graph sourceMap1134=true := by decide +kernel
theorem fusedMap1134_checked : acceptsGraphIso
    (fused (graph core1134) (root 10) 2 2) DegreeTwoThreeSpectrum6583.graph fusedMap1134=true := by decide +kernel
theorem certified1134 : Certified (graph core1134) (root 10) 2 2 :=
  of_native_maps core1134 DegreeOneMiddleResidualSpectrum2186.graph DegreeTwoThreeSpectrum6583.graph
    sourceMap1134 fusedMap1134 sourceMap1134_checked fusedMap1134_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1134
#print axioms sourceMap1134_checked
#print axioms fusedMap1134_checked
#print axioms certified1134
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
