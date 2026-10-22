/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4307 : Family 9 := level9.get ⟨372,by decide⟩
def sourceMap4307 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4307 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4307_checked : acceptsGraphIso
    (source (graph core4307) (root 9) 2 2) DegreeTwoThreeSpectrum4742.graph sourceMap4307=true := by decide +kernel
theorem fusedMap4307_checked : acceptsGraphIso
    (fused (graph core4307) (root 9) 2 2) DegreeTwoThreeSpectrum4300.graph fusedMap4307=true := by decide +kernel
theorem certified4307 : Certified (graph core4307) (root 9) 2 2 :=
  of_native_maps core4307 DegreeTwoThreeSpectrum4742.graph DegreeTwoThreeSpectrum4300.graph
    sourceMap4307 fusedMap4307 sourceMap4307_checked fusedMap4307_checked
    DegreeTwoThreeFiniteComparisons.comparison4307
#print axioms sourceMap4307_checked
#print axioms fusedMap4307_checked
#print axioms certified4307
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
