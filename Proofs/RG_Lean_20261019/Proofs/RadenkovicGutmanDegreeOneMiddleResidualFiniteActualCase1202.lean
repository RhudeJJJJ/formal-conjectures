/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1202 : Family 10 := level10.get ⟨1800,by decide⟩
def sourceMap1202 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap1202 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,12,1,0,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1202_checked : acceptsGraphIso
    (source (graph core1202) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2358.graph sourceMap1202=true := by decide +kernel
theorem fusedMap1202_checked : acceptsGraphIso
    (fused (graph core1202) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1956.graph fusedMap1202=true := by decide +kernel
theorem certified1202 : Certified (graph core1202) (root 10) 2 2 :=
  of_native_maps core1202 DegreeOneMiddleResidualSpectrum2358.graph DegreeOneMiddleResidualSpectrum1956.graph
    sourceMap1202 fusedMap1202 sourceMap1202_checked fusedMap1202_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1202
#print axioms sourceMap1202_checked
#print axioms fusedMap1202_checked
#print axioms certified1202
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
