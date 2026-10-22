/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1099 : Family 10 := level10.get ⟨1158,by decide⟩
def sourceMap1099 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1099 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1099_checked : acceptsGraphIso
    (source (graph core1099) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2091.graph sourceMap1099=true := by decide +kernel
theorem fusedMap1099_checked : acceptsGraphIso
    (fused (graph core1099) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1642.graph fusedMap1099=true := by decide +kernel
theorem certified1099 : Certified (graph core1099) (root 10) 2 2 :=
  of_native_maps core1099 DegreeOneMiddleResidualSpectrum2091.graph DegreeOneMiddleResidualSpectrum1642.graph
    sourceMap1099 fusedMap1099 sourceMap1099_checked fusedMap1099_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1099
#print axioms sourceMap1099_checked
#print axioms fusedMap1099_checked
#print axioms certified1099
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
