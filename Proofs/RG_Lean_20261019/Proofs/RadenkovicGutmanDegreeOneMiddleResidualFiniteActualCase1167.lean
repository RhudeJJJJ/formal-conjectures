/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1167 : Family 10 := level10.get ⟨1426,by decide⟩
def sourceMap1167 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap1167 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1167_checked : acceptsGraphIso
    (source (graph core1167) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2275.graph sourceMap1167=true := by decide +kernel
theorem fusedMap1167_checked : acceptsGraphIso
    (fused (graph core1167) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1950.graph fusedMap1167=true := by decide +kernel
theorem certified1167 : Certified (graph core1167) (root 10) 2 2 :=
  of_native_maps core1167 DegreeOneMiddleResidualSpectrum2275.graph DegreeOneMiddleResidualSpectrum1950.graph
    sourceMap1167 fusedMap1167 sourceMap1167_checked fusedMap1167_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1167
#print axioms sourceMap1167_checked
#print axioms fusedMap1167_checked
#print axioms certified1167
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
