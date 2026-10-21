/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons07
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core126 : Family 8 := level8.get ⟨229,by decide⟩
def sourceMap126 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,8,9,10,2,3,4,5,6,7] (sourceLabel 8 0 0 v)
def fusedMap126 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![4,0,1,2,3,7,8,9,10,5,6] (fusedLabel 8 0 0 v)
theorem sourceMap126_checked : acceptsGraphIso
    (source (graph core126) (root 8) 0 0) SmallGeFourSpectrum073.graph
      sourceMap126=true := by decide +kernel
theorem fusedMap126_checked : acceptsGraphIso
    (fused (graph core126) (root 8) 0 0) SmallGeFourSpectrum052.graph
      fusedMap126=true := by decide +kernel
theorem certified126 : Certified (graph core126) (root 8) 0 0 :=
  of_native_maps core126 SmallGeFourSpectrum073.graph SmallGeFourSpectrum052.graph
    sourceMap126 fusedMap126 sourceMap126_checked fusedMap126_checked
    SmallGeFourComparisons.comparison126
#print axioms sourceMap126_checked
#print axioms fusedMap126_checked
#print axioms certified126
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
