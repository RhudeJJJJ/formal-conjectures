/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4301 : Family 9 := level9.get ⟨356,by decide⟩
def sourceMap4301 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4301 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4301_checked : acceptsGraphIso
    (source (graph core4301) (root 9) 2 2) DegreeTwoThreeSpectrum4724.graph sourceMap4301=true := by decide +kernel
theorem fusedMap4301_checked : acceptsGraphIso
    (fused (graph core4301) (root 9) 2 2) DegreeTwoThreeSpectrum4266.graph fusedMap4301=true := by decide +kernel
theorem certified4301 : Certified (graph core4301) (root 9) 2 2 :=
  of_native_maps core4301 DegreeTwoThreeSpectrum4724.graph DegreeTwoThreeSpectrum4266.graph
    sourceMap4301 fusedMap4301 sourceMap4301_checked fusedMap4301_checked
    DegreeTwoThreeFiniteComparisons.comparison4301
#print axioms sourceMap4301_checked
#print axioms fusedMap4301_checked
#print axioms certified4301
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
