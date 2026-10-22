/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4335 : Family 9 := level9.get ⟨443,by decide⟩
def sourceMap4335 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4335 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4335_checked : acceptsGraphIso
    (source (graph core4335) (root 9) 2 2) DegreeTwoThreeSpectrum4820.graph sourceMap4335=true := by decide +kernel
theorem fusedMap4335_checked : acceptsGraphIso
    (fused (graph core4335) (root 9) 2 2) DegreeTwoThreeSpectrum4451.graph fusedMap4335=true := by decide +kernel
theorem certified4335 : Certified (graph core4335) (root 9) 2 2 :=
  of_native_maps core4335 DegreeTwoThreeSpectrum4820.graph DegreeTwoThreeSpectrum4451.graph
    sourceMap4335 fusedMap4335 sourceMap4335_checked fusedMap4335_checked
    DegreeTwoThreeFiniteComparisons.comparison4335
#print axioms sourceMap4335_checked
#print axioms fusedMap4335_checked
#print axioms certified4335
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
