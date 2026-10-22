/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1169 : Family 10 := level10.get ⟨1436,by decide⟩
def sourceMap1169 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap1169 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1169_checked : acceptsGraphIso
    (source (graph core1169) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2282.graph sourceMap1169=true := by decide +kernel
theorem fusedMap1169_checked : acceptsGraphIso
    (fused (graph core1169) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1952.graph fusedMap1169=true := by decide +kernel
theorem certified1169 : Certified (graph core1169) (root 10) 2 2 :=
  of_native_maps core1169 DegreeOneMiddleResidualSpectrum2282.graph DegreeOneMiddleResidualSpectrum1952.graph
    sourceMap1169 fusedMap1169 sourceMap1169_checked fusedMap1169_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1169
#print axioms sourceMap1169_checked
#print axioms fusedMap1169_checked
#print axioms certified1169
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
