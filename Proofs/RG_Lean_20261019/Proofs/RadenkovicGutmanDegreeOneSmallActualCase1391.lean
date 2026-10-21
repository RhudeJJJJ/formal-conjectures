/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1391 : Family 9 := level9.get ⟨140,by decide⟩
def sourceMap1391 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 9 0 0 v)
def fusedMap1391 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1391_checked : acceptsGraphIso
    (source (graph core1391) (root 9) 0 0) DegreeOneSmallSpectrum620.graph sourceMap1391=true := by decide +kernel
theorem fusedMap1391_checked : acceptsGraphIso
    (fused (graph core1391) (root 9) 0 0) DegreeOneSmallSpectrum403.graph fusedMap1391=true := by decide +kernel
theorem certified1391 : Certified (graph core1391) (root 9) 0 0 :=
  of_native_maps core1391 DegreeOneSmallSpectrum620.graph DegreeOneSmallSpectrum403.graph
    sourceMap1391 fusedMap1391 sourceMap1391_checked fusedMap1391_checked
    DegreeOneSmallComparisons.comparison1391
#print axioms sourceMap1391_checked
#print axioms fusedMap1391_checked
#print axioms certified1391
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
