/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1133 : Family 10 := level10.get ⟨1297,by decide⟩
def sourceMap1133 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1133 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1133_checked : acceptsGraphIso
    (source (graph core1133) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2185.graph sourceMap1133=true := by decide +kernel
theorem fusedMap1133_checked : acceptsGraphIso
    (fused (graph core1133) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1750.graph fusedMap1133=true := by decide +kernel
theorem certified1133 : Certified (graph core1133) (root 10) 2 2 :=
  of_native_maps core1133 DegreeOneMiddleResidualSpectrum2185.graph DegreeOneMiddleResidualSpectrum1750.graph
    sourceMap1133 fusedMap1133 sourceMap1133_checked fusedMap1133_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1133
#print axioms sourceMap1133_checked
#print axioms fusedMap1133_checked
#print axioms certified1133
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
