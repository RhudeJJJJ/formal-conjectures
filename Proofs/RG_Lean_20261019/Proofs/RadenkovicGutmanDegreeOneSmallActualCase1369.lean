/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1369 : Family 9 := level9.get ⟨117,by decide⟩
def sourceMap1369 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,5,6,7,3,4] (sourceLabel 9 0 0 v)
def fusedMap1369 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap1369_checked : acceptsGraphIso
    (source (graph core1369) (root 9) 0 0) SmallGeFourSpectrum096.graph sourceMap1369=true := by decide +kernel
theorem fusedMap1369_checked : acceptsGraphIso
    (fused (graph core1369) (root 9) 0 0) SmallGeFourSpectrum111.graph fusedMap1369=true := by decide +kernel
theorem certified1369 : Certified (graph core1369) (root 9) 0 0 :=
  of_native_maps core1369 SmallGeFourSpectrum096.graph SmallGeFourSpectrum111.graph
    sourceMap1369 fusedMap1369 sourceMap1369_checked fusedMap1369_checked
    DegreeOneSmallComparisons.comparison1369
#print axioms sourceMap1369_checked
#print axioms fusedMap1369_checked
#print axioms certified1369
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
