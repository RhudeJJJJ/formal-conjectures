/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1150 : Family 10 := level10.get ⟨1348,by decide⟩
def sourceMap1150 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1150 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1150_checked : acceptsGraphIso
    (source (graph core1150) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2223.graph sourceMap1150=true := by decide +kernel
theorem fusedMap1150_checked : acceptsGraphIso
    (fused (graph core1150) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1785.graph fusedMap1150=true := by decide +kernel
theorem certified1150 : Certified (graph core1150) (root 10) 2 2 :=
  of_native_maps core1150 DegreeOneMiddleResidualSpectrum2223.graph DegreeOneMiddleResidualSpectrum1785.graph
    sourceMap1150 fusedMap1150 sourceMap1150_checked fusedMap1150_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1150
#print axioms sourceMap1150_checked
#print axioms fusedMap1150_checked
#print axioms certified1150
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
