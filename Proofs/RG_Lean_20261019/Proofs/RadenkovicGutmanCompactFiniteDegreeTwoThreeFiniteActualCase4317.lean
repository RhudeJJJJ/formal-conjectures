/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4317 : Family 9 := level9.get ⟨399,by decide⟩
def sourceMap4317 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4317 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4317_checked : acceptsGraphIso
    (source (graph core4317) (root 9) 2 2) DegreeTwoThreeSpectrum4774.graph sourceMap4317=true := by decide +kernel
theorem fusedMap4317_checked : acceptsGraphIso
    (fused (graph core4317) (root 9) 2 2) DegreeTwoThreeSpectrum4354.graph fusedMap4317=true := by decide +kernel
theorem certified4317 : Certified (graph core4317) (root 9) 2 2 :=
  of_native_maps core4317 DegreeTwoThreeSpectrum4774.graph DegreeTwoThreeSpectrum4354.graph
    sourceMap4317 fusedMap4317 sourceMap4317_checked fusedMap4317_checked
    DegreeTwoThreeFiniteComparisons.comparison4317
#print axioms sourceMap4317_checked
#print axioms fusedMap4317_checked
#print axioms certified4317
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
